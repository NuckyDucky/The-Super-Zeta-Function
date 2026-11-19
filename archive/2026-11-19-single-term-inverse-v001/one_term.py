"""Blind inversion on the clockwise sixth branch. Python 3.12, python-flint 0.9.0.

Run encode, decode, score in order. The decoder reads only the packet file
and the same general-purpose certified zero-tracking routines for every b.
It starts at the elementary seed, with no crossing point or angle supplied.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from flint import acb, acb_series, arb, ctx


HERE = Path(__file__).resolve().parent
from layout import OUTPUT, PREVIOUS, TRANSPORT

FIRST, LAST = F(1,6), F(1,4)


def ball(q):
    return arb(q.numerator)/q.denominator


def unpack(o):
    return acb(arb(o["real"]),arb(o["imag"]))


def packed(z, digits=18):
    return {"real":z.real.str(digits), "imag":z.imag.str(digits)}


def load(path):
    return json.loads(path.read_bytes())


def save(path,data):
    path.write_text(json.dumps(data,indent=2,allow_nan=False)+"\n",encoding="utf-8")


def encode(crossing):
    ref = load(crossing)["bounds"]
    shared = acb(arb(ref["sigma"]),arb(ref["T"]))
    packets = []
    for label in ("alpha2","alpha1"):
        term = shared.zeta(ball(FIRST)+arb(ref[label])/180)
        packet = packed(term,14)
        assert unpack(packet).contains(term)
        packets.append(packet)
    return packets


def chart(w,b):
    variable = acb_series([w,1],2)
    m,n = variable.zeta(b)[1],variable.zeta(1-b)[1]
    p = -w*(w+1).zeta(b)
    r = w*(w+1).zeta(1-b)
    hw = m+n
    wb = -(p+r)/hw
    ab = (p*n-m*r)/hw
    assert not hw.contains(0) and not wb.contains(0) and not ab.contains(0)
    return wb,ab


def recover(packets, helpers):
    sys.path.insert(0,str(helpers))
    from arithmetic_reference import disk_check
    from arithmetic_holdout_replay import centered_tube
    seed = acb(0,12*arb.pi()/arb(3).log())
    radius = arb("1e-29")
    node = seed.mid()
    assert abs(seed-node)<radius and disk_check(node,radius,ball(FIRST))[2]
    targets = [unpack(p) for p in packets]
    possible = [[] for z in targets]
    # Uniform startup partitions are independent of the input readings.
    cuts = [FIRST+(LAST-FIRST)*i/192 for i in range(193)]
    pending = list(reversed(list(zip(cuts,cuts[1:]))))
    cells = 0
    while pending:
        l,r = pending.pop()
        tube = centered_tube(node,radius,l,r)
        if tube:
            end,_,rad,center = tube
            span = ball(l).union(ball(r))
            w = center + acb(arb(0,rad),arb(0,rad))
            # Mean-value enclosure on the zero disk times the parameter interval.
            # The center of the disk need not be a zero.
            mid = ball((l+r)/2)
            direct = w.zeta(span)
            hits = [i for i,z in enumerate(targets) if z.overlaps(direct)]
            if hits:
                aw = acb_series([w,1],2).zeta(span)[1]
                error = (rad*abs(aw)+ball((r-l)/2)*abs(center*(center+1).zeta(span))).upper()
                value = center.zeta(mid)+acb(arb(0,error),arb(0,error))
                hits = [i for i in hits if targets[i].overlaps(value)]
            if not hits or r-l<=F(1,10**14):
                for i in hits:
                    possible[i].append((l,r,w))
                cells += 1
                node = end
                continue
        assert r-l>F(1,10**18)
        m = (l+r)/2
        pending.extend([(m,r),(l,m)])
    entries = []
    for leaves in possible:
        assert leaves and all(x[1]==y[0] for x,y in zip(leaves,leaves[1:]))
        b = ball(leaves[0][0]).union(ball(leaves[-1][1]))
        w = leaves[0][2]
        for _,_,z in leaves[1:]:
            w = acb(w.real.union(z.real), w.imag.union(z.imag))
        v,ab = chart(w,b)
        assert not ab.real.contains(0) or not ab.imag.contains(0)
        entries.append(dict(b=b.str(22), h=(180*(b-ball(FIRST))).str(20), w=packed(w),
                            velocity=packed(v/180),heading_degrees=(v.arg()*180/arb.pi()).str(18),
                            dA_db=packed(ab),dA_dw_on_branch=packed(ab/v),
                            accepted_cells=cells, candidate_cells=len(leaves)))
    return entries


def main():
    ctx.prec,ctx.cap=224,3
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("action",choices=["encode","decode","score"])
    parser.add_argument("--crossing",type=Path,default=PREVIOUS/"revisit.json")
    parser.add_argument("--helpers",type=Path,default=TRANSPORT/"Dottie-Off-Axis-Return")
    args = parser.parse_args()
    packet_path, answer = OUTPUT/"packets.json", OUTPUT/"decoded.json"
    if args.action=="encode":
        save(packet_path,encode(args.crossing))
    elif args.action=="decode":
        readings = load(packet_path)
        assert all(set(x)=={"real","imag"} for x in readings)
        save(answer,recover(readings,args.helpers))
    else:
        expected,decoded = load(args.crossing)["bounds"],load(answer)
        visits = []
        for row in decoded:
            h = arb(row["h"])
            ids = [i for i in (1,2) if h.overlaps(arb(expected[f"alpha{i}"]))]
            assert len(ids)==1
            i = ids[0]
            assert unpack(row["w"]).contains(acb(arb(expected["sigma"]),arb(expected["T"])))
            assert arb(row["heading_degrees"]).overlaps(arb(expected[f"direction{i}_deg"]))
            visits.append(i)
        assert sorted(visits)==[1,2]
        print("Recovered visits in input order:",visits)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled.")
    main()
