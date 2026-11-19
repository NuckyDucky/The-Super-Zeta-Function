"""Independent directed checks of a sealed sweep; no target zero is input.

Usage: python -B audit_endpoint.py previous.json sealed.json --out audit.json
The previous terminal and the new start are compared in one isolating disk.
All saved nodes are audited separately with the bare bilateral Hurwitz sum.
The argument principle on a square identifies the exact finite endpoint.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def point(item):
    return acb(arb(item["real"]), arb(item["imag"]))


def endpoint(record):
    return point(record.get("terminal") or record["terminal_box"])


def jet(w, b):
    v = acb_series([w, 1], 2)
    return v.zeta(b) + v.zeta(1-b) if b is not None else v.zeta()


def val(w, b):
    return w.zeta(b) + w.zeta(1-b) if b is not None else w.zeta()


def isolate(w, radius, b):
    c = w.mid()
    assert abs(w-c) < radius
    z = jet(c,b)
    d = z[1].mid()
    square = c + acb(arb(0,radius),arb(0,radius))
    ratio = (abs(z[0])/radius + abs(jet(square,b)[1]-d))/abs(d)
    assert ratio < 1
    return ratio


def winding(center, radius, b):
    """Certified continuous change of argument on a positively oriented square."""
    corners = [center+radius*acb(x,y) for x,y in ((-1,-1),(1,-1),(1,1),(-1,1),(-1,-1))]
    bounds = center + acb(arb(0,radius),arb(0,radius))
    derivative = jet(bounds,b)[1]
    steps = 8
    angle = arb(0)
    for start, end in zip(corners,corners[1:]):
        delta = (end-start)/steps
        for j in range(steps):
            a = start + j*delta
            fa, fb = val(a,b), val(a+delta,b)
            # For every 0<=u<=1, f(a+u*delta)/f(a) belongs to this disk
            # about 1, so the change of argument uses the principal branch.
            assert abs(delta)*abs(derivative) < abs(fa)
            angle += (fb/fa).arg()
    result = (angle/(2*arb.pi())).unique_fmpz()
    assert result is not None
    return int(result)


def hardy(t):
    phase = acb(arb(1)/4,t/2).lgamma().imag - (t/2)*arb.pi().log()
    z = acb(0,phase).exp()*acb(arb(1)/2,t).zeta()
    assert z.imag.contains(0)
    return z.real


def test(previous_file, sealed_file):
    prev = json.loads(previous_file.read_bytes())
    fresh = json.loads(sealed_file.read_bytes())
    assert fresh.get("terminal_shift",fresh.get("last_b")) == "1/4"
    prior, final = endpoint(prev), endpoint(fresh)
    nodes = fresh["checkpoints"]
    start = point(nodes[0]["zero"])
    r = arb(2)**-28
    assert abs(prior-start.mid()) < r
    reset_count = winding(start.mid(),r,arb(1)/6)
    assert reset_count == 1
    # By the exact reset identity the certified previous terminal is a zero
    # of the new b=1/6 reference, so isolation identifies the new seed.
    last_shift = None
    worst = arb(0)
    for node in nodes:
        shift = Fraction(node.get("shift") or node["b"])
        assert (last_shift is None and shift == Fraction(1,6)) or (last_shift is not None and shift > last_shift)
        last_shift = shift
        b = arb(shift.numerator)/shift.denominator
        worst = max(worst,isolate(point(node["zero"]),r,b).upper())
    assert last_shift == Fraction(1,4)
    last_node = point(nodes[-1]["zero"])
    data = {"bits":ctx.prec,"sealed_sha256":hashlib.sha256(sealed_file.read_bytes()).hexdigest(),
            "previous_sha256":hashlib.sha256(previous_file.read_bytes()).hexdigest(),
            "start_winding":reset_count,"sample_disks":len(nodes),
            "maximum_sample_Rouche_ratio":worst.str(18),"audit_radius":"2^-28"}
    if abs(final.real) < r:
        n = int((final.imag*arb(2).log()/(2*arb.pi())).mid().round().unique_fmpz())
        exact = acb(0,2*n*arb.pi()/arb(2).log())
        center = exact.mid()
        assert abs(exact-center)<r and n!=0
        data.update(endpoint_kind="2^w-1",index=n,exact_imag=exact.imag.str(30))
    elif abs(final.real-arb(1)/2)<r:
        center = acb(arb(1)/2,final.imag.mid())
        data.update(endpoint_kind="Riemann")
    else:
        center = final.mid()
        data.update(endpoint_kind="off-line")
    assert abs(final-center)<r and abs(last_node-center)<r
    assert winding(center,r,arb(1)/4)==1
    data["terminal_Hurwitz_winding"]=1
    count=winding(center,r,None) if data["endpoint_kind"]!="2^w-1" else 0
    if data["endpoint_kind"]=="2^w-1":
        box=center+acb(arb(0,r),arb(0,r))
        bound=abs(box.zeta())
        assert bound>0
        data["zeta_magnitude_on_square"]=bound.str(24)
    else:
        assert count==1
        # Full-strip counts plus Hardy signs independently identify the index.
        lo,hi=center.imag.mid()-8*r,center.imag.mid()+8*r
        nlo,nhi=(v.zeta_nzeros().unique_fmpz() for v in (lo,hi))
        assert nlo is not None and nhi is not None
        data.update(total_counts=[int(nlo),int(nhi)],bracket=[lo.str(30),hi.str(30)])
        if data["endpoint_kind"]=="Riemann":
            assert nhi==nlo+1
            zlo,zhi=hardy(lo),hardy(hi)
            assert zlo*zhi<0
            data.update(ordinal=int(nhi),Hardy_values=[zlo.str(20),zhi.str(20)])
    data["terminal_Riemann_count"]=count
    return data


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("previous",type=Path)
    p.add_argument("sealed",type=Path)
    p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    ctx.prec=320
    ctx.cap=2
    report=json.dumps(test(args.previous,args.sealed),indent=2)+"\n"
    args.out.write_text(report,encoding="utf-8")
    print(report)
