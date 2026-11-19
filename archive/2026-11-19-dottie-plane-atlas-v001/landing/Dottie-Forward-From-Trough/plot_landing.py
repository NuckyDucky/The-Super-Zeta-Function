"""Display the scored endpoints and the matched single-reading errors."""
import json
from fractions import Fraction
from pathlib import Path
from statistics import median

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from flint import arb

HERE=Path(__file__).resolve().parent
SINGLE=HERE.parent/"Dottie-Blind-Landing"
def get(path): return json.loads(path.read_bytes())
def center(text): return float(arb(text).mid())
def point(pair): return complex(center(pair["real"]),center(pair["imag"]))


def plot():
    details=get(SINGLE/"scores.json")["details"]
    packets=get(SINGLE/"predictions.json")["cases"]
    cut=next(p for p in packets if p["case"]==6 and p["cutoff"]=="trough")
    dest=point(next(r["true_w"] for r in details if r["case"]==6))
    z,v,a=map(point,(cut["z"],cut["v"],cut["a"]))
    h=center(cut["h"])
    d=15-h
    ts=[d*k/120 for k in range(121)]
    pred=[z+t*v+t*t*a/2 for t in ts]
    trace=get(HERE.parent/"Dottie-Turn-Geometry"/"ten"/"summary-6.json")["samples"]
    path=[z]+[complex(x,y) for t,x,y,*_ in trace if t>h]
    plt.rcParams.update({"font.size":10.5,"axes.spines.top":False,"axes.spines.right":False})
    fig,(ax,bx)=plt.subplots(1,2,figsize=(11.3,4.55),layout="constrained",gridspec_kw={"width_ratios":[1.09,1]})
    ink,ochre,green="#174866","#b94c25","#006d70"
    ax.plot([p.real for p in path],[p.imag for p in path],color=ink,lw=2.6,label="Continued root")
    ax.plot([p.real for p in pred],[p.imag for p in pred],color=ochre,ls="--",lw=1.9,label="Trough position, velocity and acceleration")
    ax.plot([z.real,(z+d*v).real],[z.imag,(z+d*v).imag],ls=":",color="#666666",label="Trough tangent")
    ax.scatter([z.real,dest.real],[z.imag,dest.imag],color=ink,s=30,zorder=4)
    ax.scatter([pred[-1].real],[pred[-1].imag],marker="X",s=63,color=ochre,zorder=4)
    ax.annotate("Trough",(z.real,z.imag),xytext=(-3,-16),textcoords="offset points")
    ax.annotate("Sixth zero",(dest.real,dest.imag),xytext=(-6,8),textcoords="offset points",ha="right")
    ax.annotate("Estimate",(pred[-1].real,pred[-1].imag),xytext=(0,7),textcoords="offset points",ha="center",color=ochre)
    ax.set(xlim=(-.26,.64),ylim=(37.17,37.64),xlabel="Real part",ylabel="Height",title="From the last trough, one reading misses high curvature")
    ax.ticklabel_format(axis="y", useOffset=False)
    ax.legend(loc="upper left",frameon=False,fontsize=8.7)
    cutoffs=["1/16","1/8","1/4","1/2","1","trough"]
    x=[float(Fraction(k)) if k!="trough" else d for k in cutoffs]
    for name,color,style,ids in [
            ("Five speeding up · median",green,"o-",{1,2,5,8,10}),
            ("Five slowing down · median",ink,"s--",{3,4,6,7,9}),
            ("Sixth path",ochre,"^:",{6})]:
        errors=[median(center(r["methods"]["quadratic"]["complex_error"]) for r in details if r["cutoff"]==cutoff and r["case"] in ids) for cutoff in cutoffs]
        bx.loglog(x,errors,style,color=color,label=name,lw=2,ms=5)
    bx.set_xticks(x,["1/16","1/8","1/4","1/2","1","1.59"])
    bx.minorticks_off()
    bx.set(xlabel="Degrees left at the reading",ylabel="Distance from predicted to actual zero",
           title="Taking the reading closer improves all ten")
    bx.legend(loc="upper left",frameon=False,fontsize=9)
    for p in (ax,bx):
        p.grid(axis="y",color="#dce2e5",lw=.75)
        p.set_axisbelow(True)
    fig.savefig(HERE/"masked-landing.png",dpi=175)
    plt.close(fig)


if __name__=="__main__": plot()
