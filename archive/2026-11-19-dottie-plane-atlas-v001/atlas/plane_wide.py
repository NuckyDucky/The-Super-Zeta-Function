"""Wider initial plane at the same sixth-path angular cutoff. Run from any directory."""
import argparse
import json
from pathlib import Path
import numpy as np
from plane_map import HERE, compute, mark_unresolved


def plot(out,close_data):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import TwoSlopeNorm
    from matplotlib.patches import Rectangle
    from matplotlib.ticker import MultipleLocator

    g=np.load(out/"plane_wide.npz")
    close=np.load(close_data)
    report=json.loads((out/"plane_wide.json").read_bytes())
    x,y=g["x"],g["y"]
    ok=g["accepted"]
    loc=np.add.outer(1j*y,x)
    old=np.add.outer(1j*close["y"],close["x"])[~close["accepted"]]
    counts=(int(ok.sum()),int((~ok).sum()))
    minrat,maxrat=report["accepted_min_length_ratio"],report["accepted_max_length_ratio"]
    assert x[0]==-2 and x[-1]==2 and y[0]==34 and y[-1]==40 and ok.shape==(241,161)
    # A self-contained example of an accepted, almost-neutral seed.
    neutral=-1+38.65j
    nidx=np.unravel_index(np.argmin(abs(loc-neutral)),loc.shape)
    ratio=2**g["log2_length"][nidx]
    assert ok[nidx] and abs(loc[nidx]-neutral)<1e-10 and abs(ratio-1)<.0001
    ink="#192e38"; muted="#49616a"; blue="#19657d"; paper="#faf9f5"
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":11,"axes.labelcolor":ink,
                         "text.color":ink,"xtick.color":muted,"ytick.color":muted,"axes.edgecolor":"#81918f"})
    fig=plt.figure(figsize=(10.5,9.15),facecolor=paper)
    fig.text(.067,.946,"The sixth path in a wider complex plane",fontsize=24,fontweight="bold")
    fig.text(.067,.903,"A new 38,801-point grid. The return-lift angle runs from 13.40917° to 15° clockwise.",
             fontsize=12.2,color=muted)
    ax=fig.add_axes([.081,.17,.505,.665])
    ax.set_aspect("equal",adjustable="box")
    cmap=plt.get_cmap("PuOr_r").copy();cmap.set_bad("#a5aaa8")
    im=ax.pcolormesh(x,y,np.ma.array(g["log2_length"],mask=~ok),shading="nearest",
                     cmap=cmap,norm=TwoSlopeNorm(vcenter=0,vmin=np.log2(minrat),vmax=np.log2(maxrat)),rasterized=True)
    ax.set_xlim(x[0]-.0125,x[-1]+.0125);ax.set_ylim(y[0]-.0125,y[-1]+.0125)
    ax.set_xlabel("Starting real part of w");ax.set_ylabel("Starting imaginary part of w")
    ax.xaxis.set_major_locator(MultipleLocator(1));ax.yaxis.set_major_locator(MultipleLocator(1))
    # The rings show the finer predecessor data even where that point is
    # between nodes of the new grid. The twelve shared unresolved nodes
    # carry a ring and a cross at the same point.
    ax.scatter(old.real,old.imag,s=27,marker="o",facecolors="none",edgecolors=blue,lw=.9,zorder=4)
    mark_unresolved(ax,x,y,ok,8)
    ax.add_patch(Rectangle((close["x"][0],close["y"][0]),np.ptp(close["x"]),np.ptp(close["y"]),
                           fc="none",ec=blue,lw=1.55,linestyle="--",zorder=5))
    track=g["marked_w"]
    ax.plot(track.real,track.imag,lw=3.7,color="white",zorder=6)
    ax.plot(track.real,track.imag,lw=1.6,color=ink,zorder=7)
    ax.plot(track[0].real,track[0].imag,"o",mfc="white",mec=ink,ms=5,zorder=8)
    ax.plot(track[-1].real,track[-1].imag,"*",mfc=ink,mec="white",ms=11,mew=.6,zorder=8)
    ax.plot(neutral.real,neutral.imag,"o",mfc="white",mec=ink,ms=5,zorder=8)
    def callout(text,xy,xytext,color):
        ax.annotate(text,xy=xy,xytext=xytext,fontsize=9.5,ha="left",va="center",color=color,
                    arrowprops=dict(arrowstyle="-|>",lw=.95,color=color,shrinkA=3,shrinkB=4),
                    bbox=dict(boxstyle="round,pad=.2",fc=paper,ec="none",alpha=.95),zorder=10)
    callout("Original staircase",(-.33,36.96),(-1.88,36.41),blue)
    callout("Close-up area",(.64,37.93),(.68,38.28),blue)
    callout("Measured near 1×",(neutral.real,neutral.imag),(-1.87,39.05),ink)
    S=.585
    def txt(y,text,*,size=11,weight="normal",color=muted):
        fig.text(S,y,text,fontsize=size,fontweight=weight,color=color,va="top",linespacing=1.5)
    txt(.82,"Reading the colors and marks",size=15,weight="bold",color=ink)
    txt(.755,"Off-white means a measured ratio near 1×.\nAt −1 + 38.65i the ratio is 1.000010×.",size=10.8)
    txt(.65,"×   Unresolved by the wide grid solver",size=11.5,weight="bold",color=ink)
    txt(.605,f"{counts[1]} starts missed the required agreement\nbetween the two step sizes.",size=10.8)
    txt(.50,"○   Original close-up flags",size=11.5,weight="bold",color=blue)
    txt(.454,f"All {len(old)} blue-ringed starts were later solved\nwith interval arithmetic. Twelve fall exactly\non this wider grid and carry both marks.",size=10.8)
    txt(.327,"How much do lengths change?",size=13,weight="bold",color=ink)
    txt(.278,f"{counts[0]:,} accepted numerical readings span\n{minrat:.3f}× to {maxrat:.3f}×. Purple shrinks an initial\nlength. Orange stretches it.",size=10.8)
    txt(.165,"The black curve follows the marked zero.\nThe star is its arrival at the sixth Riemann zero.",size=9.65)
    cb=fig.colorbar(im,cax=fig.add_axes([.075,.086,.485,.022]),orientation="horizontal",
                    ticks=[-4,-3,-2,-1,0,1,2,3])
    cb.ax.set_xticklabels(["1/16×","1/8×","1/4×","1/2×","1×","2×","4×","8×"])
    cb.ax.tick_params(labelsize=9);cb.set_label("Final local length ÷ starting length")
    fig.savefig(out/"plane_wide.png",dpi=220,facecolor=paper)
    plt.close(fig)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path,default=HERE)
    p.add_argument("--close",type=Path,default=HERE/"plane_map.npz",help="Fine-grid data to overlay")
    p.add_argument("--plot-only",action="store_true")
    a=p.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    if not a.plot_only:
        compute(a.output,x=np.linspace(-2,2,161),y=np.linspace(34,40,241),prefix="plane_wide")
    plot(a.output,a.close)
