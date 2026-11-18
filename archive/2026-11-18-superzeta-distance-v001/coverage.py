"""Full-strip contour counts and disjoint Hardy-Z sign brackets at each height."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
from flint import acb, arb, ctx
from coverage_chart import ball, full_chart, harmonic_height, winding


def count_cell(k, center_offset):
    center = harmonic_height(k)
    H = center + ball(center_offset)
    evaluate, error = full_chart(H)
    narrow = Q(1,8)
    contour = winding(evaluate, (0,1), (-narrow,narrow))
    signs = {}
    def sign(y):
        if y not in signs:
            t = H+ball(y)
            theta = acb(ball("1/4"),t/2).lgamma().imag - t*arb.pi().log()/2
            value = evaluate(ball("1/2"),ball(y))*acb(0,theta).exp()
            assert value.imag.contains(0)
            if not (value.real>0 or value.real<0):
                raise ArithmeticError("Unresolved Hardy sign")
            signs[y] = 1 if value.real>0 else -1
        return signs[y]
    brackets = []
    grid = [-narrow+Q(j,256) for j in range(65)]
    for left,right in zip(grid,grid[1:]):
        sl, sr = sign(left), sign(right)
        if sl == sr:
            continue
        for _ in range(22):
            midpoint = (left+right)/2
            if sign(midpoint) == sl:
                left = midpoint
            else:
                right = midpoint
        assert -narrow < left < right < narrow
        brackets.append({"offset": [str(center_offset+left),str(center_offset+right)],
                         "endpoint_signs": [sl,sr]})
    assert all(Q(p["offset"][1])<Q(q["offset"][0]) for p,q in zip(brackets,brackets[1:]))
    # Each sign change requires at least one line zero. Equality with the
    # full-strip argument-principle count proves that all are simple.
    if len(brackets) != contour["count"]:
        raise ArithmeticError(f"Full count {contour['count']} versus {len(brackets)} line brackets")
    return {"center_offset":str(center_offset),
            "offsets":[str(center_offset-narrow),str(center_offset+narrow)],
            "uniform_chart_error":error.upper().str(20), **contour,"brackets":brackets}


def run(k):
    ctx.prec=192
    cells=[]
    for c in map(Q,("-3/8","-1/8","1/8","3/8")):
        print(f"Computing harmonic {k}, chart {c}",flush=True)
        cell=count_cell(k,c)
        print(f"Harmonic {k}, chart {c}: {cell['count']} simple line zeros",flush=True)
        cells.append(cell)
    return {"harmonic":k,"Riemann_real_range":["0","1"],
            "Riemann_height_offsets":["-1/2","1/2"],
            "H":harmonic_height(k).str(48),"precision_bits":ctx.prec,
            "chart_nodes":192,
            "full_count":sum(cell["count"] for cell in cells),"off_line_count":0,"cells":cells}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k",type=int,choices=(2,3))
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    result=run(args.k)
    with args.output.open("x",encoding="utf-8",newline="\n") as stream:
        stream.write(json.dumps(result,indent=2)+"\n")
