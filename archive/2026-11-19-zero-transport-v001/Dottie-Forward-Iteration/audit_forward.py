"""Certify a sealed sweep by the unscaled Hurwitz sum on overlapping Rouche disks.

Run after the sweep is sealed. No target ordinates are inputs. At each angle in
a cell the boundary of the joint disk satisfies |H-D(w-c)| < |D|r. Both
isolated node disks lie in that disk; the roots at their centers' parameter
values consequently belong to the same continuous simple branch.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

from flint import acb, acb_series, arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "Dottie-Third-Zero"))
from audit_endpoint import endpoint, isolate, jet, point, test, winding


def real(q):
    return arb(q.numerator) / q.denominator


def joined(a, za, b, zb, small):
    c = ((za+zb)/2).mid()
    m = real((a+b)/2)
    h = real((b-a)/2)
    span = real(a).union(real(b))
    radius = (2 * (max(abs(za-c).upper(), abs(zb-c).upper()) + small)).upper()
    if radius > arb('0.2'):
        return None
    outer = c + acb(arb(0,radius),arb(0,radius))
    base = jet(c,m)
    D = base[1].mid()
    v = acb_series([outer,1],3)
    hww = 2 * (v.zeta(span) + v.zeta(1-span))[2]
    v = acb_series([c,1],2)
    hb = -v * ((v+1).zeta(span)-(v+1).zeta(1-span))
    derivative_error = abs(base[1]-D) + h*abs(hb[1]) + radius*abs(hww)
    remainder = (abs(base[0])+h*abs(hb[0])) / radius + derivative_error
    ratio = remainder / abs(D)
    if ratio.is_finite() and ratio < 1:
        assert abs(za-c)+small < radius and abs(zb-c)+small < radius
        return ratio.upper()
    return None


def replay(previous, sealed, on_tube=None):
    record = json.loads(sealed.read_bytes())
    source = json.loads(previous.read_bytes())
    assert record["seed_sha256"] == hashlib.sha256(previous.read_bytes()).hexdigest()
    nodes = [(Fraction(row["shift"]),point(row["zero"])) for row in record["checkpoints"]]
    assert nodes[0][0] == Fraction(1,6)
    assert nodes[-1][0] == Fraction(record["terminal_shift"])
    small = arb(2)**-30
    nodes_seen = 0
    def check_node(b,z):
        nonlocal nodes_seen
        assert abs(z-z.mid()) < small
        isolate(z, small, real(b))
        nodes_seen += 1
    for b,z in nodes:
        check_node(b,z)
    assert abs(endpoint(source)-nodes[0][1].mid()) < small
    worst = arb(0)
    count = 0
    splits = 0
    for (a,za),(b,zb) in zip(nodes,nodes[1:]):
        assert a < b
        pending=[(a,za.mid(),b,zb.mid(),0)]
        while pending:
            a,za,b,zb,depth=pending.pop()
            verdict = joined(a,za,b,zb,small)
            if verdict is not None:
                if on_tube is not None:
                    on_tube(a,b,verdict)
                worst=max(worst,verdict)
                count += 1
                continue
            assert depth<25 and count<100000
            mid=(a+b)/2
            zm=((za+zb)/2).mid()
            for j in range(4):
                h=jet(zm,real(mid))
                zm=(zm-h[0]/h[1]).mid()
            check_node(mid,zm)
            pending.extend(((mid,zm,b,zb,depth+1),(a,za,mid,zm,depth+1)))
            splits += 1
    if nodes[-1][0] == Fraction(1,4) and abs(endpoint(record).real) < small:
        z=endpoint(record)
        k=(z.imag*arb(2).log()/(2*arb.pi())+arb(1)/2).floor().unique_fmpz()
        assert k is not None and k != 0
        exact=acb(0,2*int(k)*arb.pi()/arb(2).log())
        c=exact.mid()
        assert abs(exact-c) < small and abs(z-c)<small and abs(nodes[-1][1]-c)<small
        box=c+acb(arb(0,small),arb(0,small))
        magnitude=abs(box.zeta())
        assert magnitude>0
        raw_count=winding(c,small,arb(1)/4)
        zeta_count=winding(c,small,None)
        seed_count=winding(nodes[0][1].mid(),small,arb(1)/6)
        assert raw_count==1 and seed_count==1 and zeta_count==0
        data=dict(bits=ctx.prec,start_winding=seed_count,terminal_Hurwitz_winding=raw_count,
                  terminal_Riemann_count=zeta_count,endpoint_kind="2^w-1",index=int(k),
                  exact_imag=exact.imag.str(28),zeta_magnitude_on_square=magnitude.str(24))
    elif nodes[-1][0] == Fraction(1,4):
        data=test(previous,sealed)
    else:
        data = dict(start_winding=winding(nodes[0][1].mid(),small,arb(1)/6))
        assert data["start_winding"]==1
        if record["status"] == "certified escape":
            from tail_certificate import certify_escape_at
            z=endpoint(record)
            mode=certify_escape_at(nodes[-1][0],z.mid(),abs(z-z.mid()).upper())
            assert mode and mode['fourier_mode']==record['escape']['fourier_mode']
            data["escape_reproduced"]=mode
    data.update(sealed_sha256=hashlib.sha256(sealed.read_bytes()).hexdigest(),
                unscaled_rouche_tubes=count, extra_bisections=splits,
                all_isolated_nodes=nodes_seen, largest_uniform_ratio=worst.str(14))
    return data


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('previous',type=Path)
    p.add_argument('sealed',type=Path)
    p.add_argument('out',type=Path)
    args=p.parse_args()
    ctx.prec=320
    ctx.cap=3
    data=replay(args.previous,args.sealed)
    args.out.write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    print(json.dumps(data,indent=2))
