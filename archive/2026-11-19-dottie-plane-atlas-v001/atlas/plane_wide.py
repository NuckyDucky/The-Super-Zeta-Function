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
    fig=plt.figure(figsize=(12.8,9.4),facecolor=paper)
    fig.text(.065,.938,"How sensitive is the landing to the starting point?",fontsize=23,fontweight="bold",color=ink)
    fig.text(.065,.882,"Imagine nudging a starting point. Its color tells you how much that tiny nudge changes where you land.",
             fontsize=12.3,color=muted)
    ax=fig.add_axes([.063,.211,.497,.61])
    ax.set_aspect("equal",adjustable="box")
    cmap=plt.get_cmap("PuOr_r").copy();cmap.set_bad("#a5aaa8")
    im=ax.pcolormesh(x,y,np.ma.array(g["log2_length"],mask=~ok),shading="nearest",
                     cmap=cmap,norm=TwoSlopeNorm(vcenter=0,vmin=np.log2(minrat),vmax=np.log2(maxrat)),rasterized=True)
    ax.set_xlim(x[0]-.0125,x[-1]+.0125);ax.set_ylim(y[0]-.0125,y[-1]+.0125)
    ax.set_xlabel("Starting real part");ax.set_ylabel("Starting height (imaginary part)")
    ax.xaxis.set_major_locator(MultipleLocator(1));ax.yaxis.set_major_locator(MultipleLocator(1))
    # The rings show the finer predecessor data even where that point is
    # between nodes of the new grid. The twelve shared unresolved nodes
    # carry a ring and a cross at the same point.
    ax.scatter(old.real,old.imag,s=27,marker="o",facecolors="none",edgecolors=blue,lw=.9,zorder=4)
    mark_unresolved(ax,x,y,ok,8)
    track=g["marked_w"]
    ax.plot(track.real,track.imag,lw=3.7,color="white",zorder=6)
    ax.plot(track.real,track.imag,lw=1.6,color=ink,zorder=7)
    ax.plot(track[0].real,track[0].imag,"o",mfc="white",mec=ink,ms=5,zorder=8)
    ax.plot(track[-1].real,track[-1].imag,"*",mfc=ink,mec="white",ms=11,mew=.6,zorder=8)
    ax.annotate("Trough",xy=(track[0].real,track[0].imag),xytext=(4,-7),
                textcoords="offset points",ha="left",va="top",fontsize=9.5,fontweight="bold",
                color=ink,bbox=dict(boxstyle="round,pad=.16",fc=paper,ec="none",alpha=.88),zorder=10)
    S=.555
    def txt(y,text,*,size=11,weight="normal",color=muted):
        fig.text(S,y,text,fontsize=size,fontweight=weight,color=color,va="top",linespacing=1.5)
    txt(.823,"Read one colored point",size=15.5,weight="bold",color=ink)
    txt(.778,"Follow two very close starts through the same turn.\nCompare the gap between them at the beginning and end.",size=10.6)
    key=fig.add_axes([S,.548,.394,.145])
    key.set_xlim(0,1);key.set_ylim(0,1)
    key.axis("off")
    key.text(.385,.94,"Starting gap",color=muted,fontsize=9,ha="center")
    key.text(.76,.94,"Landing gap",color=muted,fontsize=9,ha="center")
    for ratio,level,yrow in ((.5,"Purple",.69),(1,"Off-white",.40),(2,"Orange",.11)):
        # The example dots use one ruler in both columns. Each represents
        # a pair of infinitesimally close trajectories, magnified for display.
        color=im.cmap(im.norm(np.log2(ratio)))
        key.scatter(.022,yrow,marker="s",c=[color],s=96,edgecolor="#74838a",linewidth=.65)
        key.text(.064,yrow,f"{level}   {ratio:g}×",va="center",color=ink,fontsize=9.5)
        for origin,dist in ((.325,.12),(.685,.12*ratio)):
            key.plot([origin,origin+dist],[yrow,yrow],lw=1.85,color=ink,solid_capstyle="round")
            key.scatter([origin,origin+dist],[yrow,yrow],s=25,color=ink,zorder=3)
    txt(.493,"Why start at the trough?",size=15.5,weight="bold",color=ink)
    txt(.445,"The open circle is the last low point of the black path.\nIts height stops falling at 37.21583 while the point is still\nmoving sideways. From here the path rises to the star,\nthe sixth Riemann zero at height 37.58618.",size=10.6)
    txt(.313,"At that starting point the factor is 0.939×.",size=11,weight="bold",color=ink)
    txt(.273,"The marked point travels 0.801 in straight-line distance.\nA tiny gap between neighboring starts shrinks by 6.1%.\nColor measures that gap, regardless of the distance traveled.",size=10.4)
    cb=fig.colorbar(im,cax=fig.add_axes([.09,.126,.433,.016]),orientation="horizontal",
                    ticks=[-4,-3,-2,-1,0,1,2,3])
    cb.ax.set_xticklabels(["1/16×","1/8×","1/4×","1/2×","1×","2×","4×","8×"])
    cb.ax.tick_params(labelsize=8.5);cb.set_label("Landing gap ÷ starting gap, for a tiny nudge",size=10)
    txt(.155,"×  Wide-grid calculation needed refinement (152 starts).",size=9.2,color=ink)
    txt(.126,"○  Blue ring: starting point checked separately (37 starts).",size=9.2,color=blue)
    fig.text(.065,.039,"The angle changes from 13.40917° to 15°. Each start keeps its own value of the symmetric Hurwitz sum. The black path keeps value zero.",
             fontsize=9,color=muted)
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
