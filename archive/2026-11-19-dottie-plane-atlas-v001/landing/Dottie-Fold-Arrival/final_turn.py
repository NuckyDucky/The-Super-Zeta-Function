"""Enclose the speed maximum on the last clockwise degree of the sixth landing.

python-flint 0.9.0. Uses the published sixth-passes-v001 and zero-transport-v001
enclosures. By default look for their original folders beside this note; for
a public checkout use --repo PATH. All h derivatives are per clockwise degree.
"""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path

from flint import arb, ctx


HERE = Path(__file__).resolve().parent


def run(arc):
    from turning import partials
    from verify import BASE, Branch, ball, square

    ctx.prec, ctx.cap = 224, 5
    branch = Branch(arc)

    def shift(h):
        return BASE + h / 180

    def point(h):
        w, v, a = branch.node_values(shift(h))
        return w, abs(v), (v.conjugate() * a).real

    def sign_on(center, radius, left, right, order):
        # Implicit derivatives in b, then change to degrees. The speed has
        # the sign of Re(conj(v)*a) for its first derivative when |v|>0.
        b = ball(left).union(ball(right))
        d = partials(square(center,radius), b, 3)
        mid = partials(center, ball((left+right)/2), 2)
        # Center lower partials before combining them: cancellation between
        # the two Hurwitz derivatives is significant on this arc.
        for n in (2,1):
            for j in range(n+1):
                i=n-j
                err=radius*abs(d[i+1,j])+ball((right-left)/2)*abs(d[i,j+1])
                d[i,j]=square(mid[i,j],err.upper())
        v = -d[0,1] / d[1,0]
        a = -(d[2,0]*v*v + 2*d[1,1]*v + d[0,2]) / d[1,0]
        if order == 2:
            return (v.conjugate() * a).real / 180**3
        j = -(d[3,0]*v**3 + 3*d[2,1]*v*v + 3*d[1,2]*v + d[0,3]
              + 3*(d[2,0]*v + d[1,1])*a) / d[1,0]
        return (abs(a)**2 + (v.conjugate()*j).real) / 180**4

    def cover(left, right, order, sign):
        node = branch.at(shift(left))
        pending = [(left, right)]
        cells = 0
        while pending:
            l, r = pending.pop()
            b0, b1 = shift(l), shift(r)
            tube = branch.centered_tube(node, branch.radius, b0, b1)
            if tube is not None:
                end, _, radius, center = tube
                val = sign_on(center,radius,b0,b1,order)
                if sign*val > 0:
                    node = end
                    cells += 1
                    continue
            assert r-l > F(1,2**34), (l,r)
            mid = (l+r)/2
            pending.extend(((mid,r),(l,mid)))
        # Both continued roots lie in this single disk where uniqueness holds.
        assert abs(node - branch.at(shift(right))) + branch.radius < arb("1e-9")
        assert branch.disk_check(node, arb("1e-9"), ball(shift(right)))[2]
        print("Verified interval", left, right, "in", cells, "cells", flush=True)
        return cells

    left, right = F("14.69"), F("14.75")
    checks = [cover(F(14),left,2,1), cover(left,right,3,-1), cover(right,F(15),2,-1)]
    assert point(left)[2]>0 and point(right)[2]<0
    for _ in range(34):
        h = (left+right)/2
        val = point(h)[2]
        assert not val.contains(0)
        if val>0:
            left=h
        else:
            right=h
    from verify import jets
    b0,b1 = shift(left),shift(right)
    enclosure = branch.enclose(b0,b1)
    v,_ = jets(enclosure,ball(b0).union(ball(b1)))
    speed_max = abs(v)
    dest, speed_end, indicator_end = point(F(15))
    w0, speed_start, _ = point(F(14))
    return dict(precision_bits=ctx.prec, clock="clockwise degrees from 60 degrees",
                source_sha256=branch.digest,
                positive_speed_derivative_h=["14","14.69"],
                strictly_decreasing_half_squared_speed_derivative_h=["14.69","14.75"],
                negative_speed_derivative_h=["14.75","15"], accepted_cells=checks,
                maximum_h=ball(left).union(ball(right)).str(15),
                maximum_speed=speed_max.str(16), initial_speed_at_14=speed_start.str(16),
                terminal_speed=speed_end.str(16),
                terminal_speed_derivative=(indicator_end/speed_end).str(16),
                percent_drop=(100*(1-speed_end/speed_max)).str(15),
                maximum_w=dict(real=enclosure.real.str(16),imag=enclosure.imag.str(16)),
                endpoint_w=dict(real=dest.real.str(16),imag=dest.imag.str(16)))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled")
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path)
    p.add_argument("--output", type=Path, default=HERE/"final_turn.json")
    args = p.parse_args()
    if args.repo:
        archive=args.repo.resolve()/"archive"
        jets_path=archive/"2026-11-19-sixth-passes-v001"/"compute"
        arc=archive/"2026-11-19-zero-transport-v001"
    else:
        arc=HERE.parent
        jets_path=arc/"Dottie-Sixth-Passes"/"compute"
    if not (jets_path/"turning.py").is_file() and (jets_path.parent/"computations"/"turning.py").is_file():
        jets_path=jets_path.parent/"computations"
    sys.path.insert(0,str(jets_path))
    res=run(arc)
    args.output.write_text(json.dumps(res,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(res,indent=2))
