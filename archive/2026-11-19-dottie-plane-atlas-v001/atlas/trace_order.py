"""Draw the two reciprocal-root sums for the period-640 centerline orbit."""
import argparse
import hashlib
import json
from math import isclose, pi, sin, sqrt
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


SOURCE=Path("archive/2026-11-19-oriented-return-v001/data/quarter_probe.json")
DIGEST="7d3afc4ded30439ec277ef5a3636f187f1ae89ef8de5992ed77392068c1d051f"
HERE=Path(__file__).resolve().parent
BLUE,ORANGE,INK="#005785","#ad5000","#1d2930"


def number(row,key):
    """The original directed balls stay in the source. Plot their printed centers."""
    return float(row[key].lstrip("[").split()[0])


def draw(source,output):
    blob=source.read_bytes()
    if hashlib.sha256(blob).hexdigest()!=DIGEST:
        raise ValueError("The signed trace record differs from the archived quarter_probe.json.")
    record=json.loads(blob)
    before,after=(record[name] for name in ("original","clockwise"))
    b,a=(number(row,"angle_deg") for row in (before,after))
    assert record["ordered_period"]==640 and record["scalar_period"]==320
    assert a < -90 < b and isclose(a,b-30,abs_tol=1e-12)
    assert number(after,"y")!=number(before,"y")
    assert record["original_contained_in_restored_bounds"]
    left,right=a-2.2,b+4.1
    theta=np.linspace(left,right,1200)
    fig,ax=plt.subplots(figsize=(10,6))
    fig.subplots_adjust(left=.105,right=.958,top=.70,bottom=.19)
    fig.text(.105,.94,"The two spectral readings exchange order at −90°",fontsize=21,
             color=INK,fontweight="bold")
    fig.text(.105,.882,"The angle measures how a small displacement turns after one full lap of the centerline orbit.",
             fontsize=11.5,color="#4b606a")
    for key,sign,color,style,marker,lab in (
            ("trace_plus",1,BLUE,"-","o",r"$M_+$ at $\theta+30^\circ$"),
            ("trace_minus",-1,ORANGE,(0,(5,2.6)),"s",r"$M_-$ at $\theta-30^\circ$")):
        ax.plot(theta,2/(1-np.sin(np.deg2rad(theta+sign*30))),label=lab,
                c=color,ls=style,lw=2)
        for row,t in ((before,b),(after,a)):
            y=number(row,key)
            assert isclose(y,2/(1-sin((t+sign*30)*pi/180)),rel_tol=1e-13)
            ax.scatter(t,y,s=55,marker=marker,facecolor=color,edgecolor="white",zorder=5)
            offset=(6,10 if sign==1 else -11) if t==b else (8,8 if sign==1 else -8)
            ax.annotate(f"{y:.4f}",xy=(t,y),xytext=offset,textcoords="offset points",
                        color=color,fontsize=10.5,fontweight="bold",va="center",
                        bbox=dict(facecolor="white",edgecolor="none",alpha=.9,pad=.65))
    for x,label,alignment in ((a,"Same period-640 branch after the turn","left"),
                              (b,"Centerline period-640 orbit before the turn","right")):
        ax.axvline(x,color="#a4afb4",lw=.95,ls=(0,(2,3)),zorder=0)
        ax.text(x,1.025,label,transform=ax.get_xaxis_transform(),ha=alignment,
                va="bottom",fontweight="bold",color=INK,fontsize=10)
    arrow_y=1.303
    ax.annotate("",xy=(a+.9,arrow_y),xytext=(b-.5,arrow_y),
                arrowprops=dict(arrowstyle="->",color=INK,lw=1))
    ax.text((a+b)/2,arrow_y,"30° clockwise",ha="center",va="center",fontsize=10,
            bbox=dict(facecolor="white",edgecolor="none",pad=2))
    pivot=8-4*sqrt(3)
    ax.scatter(-90,pivot,marker="D",facecolor="white",edgecolor=INK,lw=1.2,s=41,zorder=6)
    ax.annotate(r"$M_+=M_-=8-4\sqrt{3}$",xy=(-90,pivot),xytext=(-97,1.179),
                ha="center",fontsize=11,arrowprops=dict(arrowstyle="-",color=INK,lw=.85,shrinkB=5))
    ax.set(xlim=(left,right),ylim=(.982,1.32),ylabel="First reciprocal-root sum",
           xlabel=r"Return angle $\theta$ (degrees)")
    ax.set_xticks([a,-110,-100,-90,b],labels=[f"−{abs(a):.2f}","−110","−100","−90",f"−{abs(b):.2f}"])
    ax.set_yticks([1,1.05,1.10,1.15,1.20,1.25,1.30])
    ax.grid(axis="y",color="#e1e6e8",lw=.75)
    ax.spines[["right","top"]].set_visible(False)
    ax.tick_params(colors=INK,labelsize=10,length=3)
    ax.legend(loc="upper left",bbox_to_anchor=(.101,.855),bbox_transform=fig.transFigure,
              ncol=2,frameon=False,borderaxespad=0,handlelength=2.5,columnspacing=2.5)
    fig.text(.105,.052,
             f"Centerline parameter y changes from {number(before,'y'):.15f} to {number(after,'y'):.15f}.",
             color="#4b606a",fontsize=10.2)
    output.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(output,dpi=240,facecolor="white",
                metadata={"Title":"Centerline period-640 orbit before and after a 30 degree clockwise turn"})
    plt.close(fig)


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo",type=Path,help="Path to The Super Zeta Function checkout.")
    cli.add_argument("--data",type=Path,help="The archived quarter_probe.json.")
    cli.add_argument("--output",type=Path,default=HERE/"trace_order.png")
    args=cli.parse_args()
    source=args.data
    if source is None:
        repo=args.repo or next((p for p in HERE.parents if (p/SOURCE).is_file()),None)
        if repo is None: cli.error("Supply --repo or --data.")
        source=repo/SOURCE
    draw(source,args.output)
