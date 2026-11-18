"""Certify lower bounds for the reconstructed superzeta per unit distance to a zero."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path

from flint import acb, arb, ctx
from coverage_chart import ball, full_chart, harmonic_height


def interval(a, b):
    return ball(a).union(ball(b))


def certify(k, record):
    ctx.prec = 192
    H = harmonic_height(k)
    if (record["harmonic"] != k or record["Riemann_real_range"] != ["0", "1"]
            or record["Riemann_height_offsets"] != ["-1/2", "1/2"]):
        raise ValueError("Incorrect coverage region")
    half = Q(1, 2)
    brackets = [tuple(map(Q, bracket["offset"])) for cell in record["cells"]
                for bracket in cell["brackets"]]
    assert len(brackets) == record["full_count"] and brackets
    assert all(-half < lo < hi < half for lo, hi in brackets)
    assert all(a[1] < b[0] for a, b in zip(brackets, brackets[1:]))
    cuts = [-half, *((a[1] + b[0])/2 for a, b in zip(brackets, brackets[1:])), half]
    centers = [Q(j, 8) for j in (-3, -1, 1, 3)]
    log2, logpi = arb(2).log(), arb.pi().log()

    @lru_cache(maxsize=4)
    def chart(center):
        return full_chart(H + ball(center))[0]

    def edge(center, start, end, root, depth=0):
        x0, y0 = start
        x1, y1 = end
        beta = interval(min(x0, x1), max(x0, x1))
        y = interval(min(y0, y1), max(y0, y1))
        zeta = chart(center)(beta, y - ball(center))
        # |F(w/2)| = 2 pi^(-beta) |2^w-1| |zeta(w)|, also on beta=0.
        phase = (acb(beta, H+y)*log2).exp() - 1
        numerator = 2*(-beta*logpi).exp()*abs(phase)*abs(zeta)
        denominator = abs(acb(beta-ball(half), y-root))
        if denominator > 0:
            ratio = numerator/denominator
            if ratio.lower() > 0 and ratio.lower() > 3*ratio.upper()/4:
                return ratio.lower(), 1
        if depth >= 24:
            raise ArithmeticError("Could not certify the edge")
        mid = ((x0+x1)/2, (y0+y1)/2)
        left, nl = edge(center, start, mid, root, depth+1)
        right, nr = edge(center, mid, end, root, depth+1)
        return min(left, right), nl+nr

    cells = []
    for idx, (bracket, lo, hi) in enumerate(zip(brackets, cuts, cuts[1:]), start=1):
        root = interval(*bracket)
        assert lo < bracket[0] < bracket[1] < hi
        sides = []
        for y in (lo, hi):
            center = next(c for c in centers if abs(y-c) <= Q(1,8))
            sides.append(edge(center, (Q(0),y), (Q(1),y), root))
        for center in centers:
            a, b = max(lo, center-Q(1,8)), min(hi, center+Q(1,8))
            if a < b:
                for x in (Q(0), Q(1)):
                    sides.append(edge(center, (x,a), (x,b), root))
        low = min(v for v,_ in sides)
        units = (low*1024).floor().unique_fmpz()
        assert units is not None and units > 0
        lower = Q(int(units),1024)
        assert low >= ball(lower)
        cells.append({"index":idx, "height_offset_cell":[str(lo),str(hi)],
                      "root_height_offset_bracket":list(map(str,bracket)),
                      "factor_lower_bound_w_units":str(lower),
                      "certified_boundary_segments":sum(n for _,n in sides)})

    common = min(Q(c["factor_lower_bound_w_units"]) for c in cells)
    return {"harmonic":k, "precision_bits":ctx.prec, "cell_count":len(cells),
            "distance_coefficient_w":str(common), "distance_coefficient_s":str(2*common),
            "cells":cells}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coverage", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.coverage.read_bytes())
    result = certify(data["harmonic"], data)
    with args.output.open("x", encoding="utf-8", newline="\n") as out:
        out.write(json.dumps(result, indent=2)+"\n")
    print("Harmonic", result["harmonic"], "bound in s units", result["distance_coefficient_s"])
