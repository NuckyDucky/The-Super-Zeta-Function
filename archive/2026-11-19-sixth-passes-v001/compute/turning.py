"""Enclose the signed angular velocity and count horizontal tangencies on the sixth branch."""
import argparse
import json
from pathlib import Path

from math import factorial
from flint import acb, acb_series, arb, ctx

from verify import BASE, F, HERE, Branch, ball, jets, sgn, source_root, square


def partials(z,b,order):
    values = {}
    for j in range(order+1):
        w = acb_series([z,1],order-j+1)
        factor = 1
        for k in range(j):
            factor *= w+k
        shift = w+j
        term = factor*((-1)**j*shift.zeta(b) + shift.zeta(1-b))
        for i in range(order-j+1):
            values[i,j] = factorial(i)*term[i]
    return values


def enclosure(center,radius,a,b):
    """Center the first and second partials. Each mean-value step uses full tube bounds."""
    span = ball(a).union(ball(b))
    mid = ball((a+b)/2)
    half = ball((b-a)/2)
    point = partials(center,mid,2)
    bound = partials(square(center,radius),span,3)
    for order in (2,1):
        for j in range(order+1):
            i = order-j
            error = (radius*abs(bound[i+1,j]) + half*abs(bound[i,j+1])).upper()
            bound[i,j] = square(point[i,j],error)
    v = -bound[0,1]/bound[1,0]
    acc = -(bound[2,0]*v*v+2*bound[1,1]*v+bound[0,2])/bound[1,0]
    return v/180, acc/(180**2)


def measure(archive):
    ctx.prec, ctx.cap = 192, 4
    branch = Branch(archive)
    start, stop = F(645, 64), F(905, 64)
    a0, b0 = BASE + start/180, BASE + stop/180
    node = branch.at(a0)
    cells = 0
    tangencies = []
    # The two coarse rational limits are asserted on every cell, including endpoints.
    work = [(a0, b0)]
    while work:
        a, b = work.pop()
        tube = branch.centered_tube(node, branch.radius, a, b)
        if tube is not None:
            end, _, radius, center = tube
            v, acc = enclosure(center,radius,a,b)
            rate = (acc/v).imag
            if rate.is_finite() and rate > arb(1)/20 and rate < 6:
                simple = not v.imag.contains(0)
                if not simple and not acc.imag.contains(0):
                    initial, _ = jets(square(node, branch.radius), ball(a))
                    final, _ = jets(square(end, branch.radius), ball(b))
                    if not initial.imag.contains(0) and not final.imag.contains(0):
                        if sgn(initial.imag) != sgn(final.imag):
                            horizontal = sgn(v.real)
                            tangencies.append(dict(angle_bracket=[str(180*(a-BASE)), str(180*(b-BASE))],
                                                   height_direction_after=sgn(final.imag), horizontal_sign=horizontal))
                        simple = True
                if simple:
                    node = end
                    cells += 1
                    continue
        assert b-a > F(1, 2**38), (a, b)
        mid = (a+b)/2
        work.extend([(mid,b), (a,mid)])
    assert [(x["height_direction_after"], x["horizontal_sign"]) for x in tangencies] == [(-1,-1), (1,1)]
    # Identify both endpoints with roots in the archived checkpoint enclosures.
    assert abs(node - branch.at(b0)) < arb("1e-28")
    return dict(source_sha256=branch.digest, precision_bits=ctx.prec,
                angle_degrees=[str(start),str(stop)], accepted_cells=cells,
                angular_rate_radians_per_degree_strict_bounds=["1/20","6"],
                tangencies=tangencies, signed_turn_between_tangencies="pi")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--output", type=Path, default=HERE/"turning.json")
    parser.add_argument("--compare", type=Path)
    args = parser.parse_args()
    result = measure(source_root(args.archive))
    if args.compare:
        old = json.loads(args.compare.read_bytes())
        for key in ("source_sha256","precision_bits","angle_degrees","angular_rate_radians_per_degree_strict_bounds",
                    "signed_turn_between_tangencies"):
            assert result[key] == old[key], key
        assert len(old["tangencies"]) == len(result["tangencies"])
        for new, prior in zip(result["tangencies"],old["tangencies"]):
            assert all(new[k] == prior[k] for k in ("height_direction_after","horizontal_sign"))
            a,b = map(F,new["angle_bracket"])
            l,r = map(F,prior["angle_bracket"])
            assert max(a,l) < min(b,r)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result)
