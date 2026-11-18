"""Locate all zeros by their global indices and check fresh line sign brackets."""
import argparse
import json
from pathlib import Path
from fractions import Fraction as Q
from flint import arb, acb, ctx
from coverage_chart import ball, harmonic_height


def compute(folder):
    source=json.loads((folder/"coverage-global-counts.json").read_text())
    results=[]
    for record in source["windows"]:
        k=record["k"]
        ctx.prec=128
        H=harmonic_height(k)
        count=record["upper_N"]-record["lower_N"]
        zeros=acb.zeta_zeros(record["lower_N"]+1, count)
        intervals=[]
        for zero in zeros:
            offset=zero.imag-H
            step=262144
            index=(step*offset).floor().unique_fmpz()
            if index is None:
                raise ArithmeticError("Ambiguous dyadic bracket")
            lo,hi=Q(int(index),step),Q(int(index)+1,step)
            assert ball(lo)<offset<ball(hi)
            assert -Q(1,2)<lo<hi<Q(1,2)
            signs=[]
            for endpoint in (lo,hi):
                t=H+ball(endpoint)
                theta=acb(ball("1/4"),t/2).lgamma().imag-t*arb.pi().log()/2
                value=acb(ball("1/2"),t).zeta()*acb(0,theta).exp()
                assert value.imag.contains(0) and (value.real>0 or value.real<0)
                signs.append(1 if value.real>0 else -1)
            assert signs[0]*signs[1]==-1
            intervals.append({"offset":[str(lo),str(hi)],"endpoint_signs":signs})
        assert len(intervals)==count and all(Q(p["offset"][1])<Q(q["offset"][0])
                                              for p,q in zip(intervals,intervals[1:]))
        results.append({**record,"brackets":intervals})
        print(f"H{k}: {count} global-index zeros located and checked.",flush=True)
    return {"precision_bits":ctx.prec,"windows":results}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",type=Path)
    opts=parser.parse_args()
    data=compute(opts.output.parent)
    with opts.output.open("x",encoding="utf-8",newline="\n") as file:
        file.write(json.dumps(data,indent=2)+"\n")
