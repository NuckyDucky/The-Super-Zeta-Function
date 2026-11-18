"""Independently check the two widened windows with FLINT's global zero counter."""
import argparse
import json
from pathlib import Path
from flint import arb, ctx
from coverage_chart import harmonic_height, ball


def run():
    ctx.prec = 96
    records=[]
    for k in (2,3):
        H=harmonic_height(k)
        integers=[]
        for side in ("-1/2","1/2"):
            # A singleton bounds the monotone N(t) throughout this guard.
            guard=H+ball(side)+arb(0,arb(2)**-18)
            count=guard.zeta_nzeros()
            val=count.unique_fmpz()
            if val is None:
                raise ArithmeticError(f"Unresolved global count near harmonic {k}, {side}")
            print(f"H{k} offset {side}, N(T) = {val}", flush=True)
            integers.append(int(val))
        records.append({"k":k,"lower_N":integers[0],"upper_N":integers[1],
                        "difference":integers[1]-integers[0]})
    return {"precision_bits":ctx.prec, "guard_radius":"1/262144", "windows":records}


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    result=run()
    with args.output.open("x",encoding="utf-8",newline="\n") as stream:
        stream.write(json.dumps(result,indent=2)+"\n")
