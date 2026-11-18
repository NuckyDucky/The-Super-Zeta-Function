"""Re-evaluate every Hardy sign without interpolation; compare to global counts."""
import argparse
import json
from fractions import Fraction
from pathlib import Path
from flint import acb, arb, ctx
from coverage_chart import ball, harmonic_height


def check(folder):
    totals=json.loads((folder/"coverage-global-counts.json").read_text())
    ctx.prec=128
    for independent in totals["windows"]:
        k=independent["k"]
        H=harmonic_height(k)
        region=json.loads((folder/f"coverage-h{k}.json").read_text())
        intervals=[]
        for cell in region["cells"]:
            for entry in cell["brackets"]:
                lo,hi=map(Fraction,entry["offset"])
                assert Fraction(-1,2)<lo<hi<Fraction(1,2)
                signs=[]
                for endpoint in (lo,hi):
                    t=H+ball(endpoint)
                    theta=acb(ball("1/4"),t/2).lgamma().imag-t*arb.pi().log()/2
                    value=acb(ball("1/2"),t).zeta()*acb(0,theta).exp()
                    assert value.imag.contains(0)
                    assert value.real>0 or value.real<0
                    signs.append(1 if value.real>0 else -1)
                assert signs[0]*signs[1]==-1 and signs==entry["endpoint_signs"]
                intervals.append((lo,hi))
        intervals.sort()
        assert all(p[1]<q[0] for p,q in zip(intervals,intervals[1:]))
        assert independent["upper_N"]-independent["lower_N"]==len(intervals)==region["full_count"]
        print(f"H{k}: {len(intervals)} disjoint Hardy sign brackets account for all zeros.")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder",nargs="?",type=Path,default=Path(__file__).resolve().parent)
    check(parser.parse_args().folder)
