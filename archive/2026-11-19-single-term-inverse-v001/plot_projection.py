"""Two projections of the same part of the sixth branch. Python-flint and matplotlib."""
from pathlib import Path
import json
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from flint import arb,ctx
from chart import Branch, ball, parameter
from layout import OUTPUT, PREVIOUS, TRANSPORT


HERE=Path(__file__).resolve().parent


def midpoint(value):
    return float(arb(value).mid())


def draw():
    ctx.prec,ctx.cap=192,3
    branch=Branch(TRANSPORT)
    points=[]
    for i in range(375,601):
        h=Fraction(i,40)
        b=parameter(h)
        w=branch.at(b)
        a=w.zeta(ball(b))
        points.append([(float(z.real.mid()),float(z.imag.mid())) for z in (w,a)])
    cross=json.loads((HERE/"chart-crossing.json").read_bytes())["bounds"]
    visits=json.loads((HERE/"packets.json").read_bytes())
    shared=json.loads((PREVIOUS/"revisit.json").read_bytes())["bounds"]
    visit_marks=[[(midpoint(shared["sigma"]),midpoint(shared["T"]))],
                 [(midpoint(x["real"]),midpoint(x["imag"])) for x in visits]]
    other_marks=[[(midpoint(cross["sigma"+str(j)]),midpoint(cross["T"+str(j)])) for j in (1,2)],
                 [(midpoint(cross["A_real"]),midpoint(cross["A_imag"]))]]
    fig,axes=plt.subplots(1,2,figsize=(10.2,4.4))
    fig.subplots_adjust(left=.08,right=.98,bottom=.25,top=.83,wspace=.30)
    teal,orange="#006a72","#ae4629"
    for j,(ax,title) in enumerate(zip(axes,["Position of the zero  w","Value of the first term  A"])):
        x,y=zip(*[p[j] for p in points])
        ax.plot(x,y,color="#414e57",lw=2.0)
        for marks,pen,shape in ((visit_marks[j],teal,"o"),(other_marks[j],orange,"D")):
            mx,my=zip(*marks)
            ax.scatter(mx,my,c=pen,edgecolor="white",s=80,linewidth=1,marker=shape,zorder=3)
        for k in (32,110,198):
            ax.annotate("",xy=(x[k+4],y[k+4]),xytext=(x[k],y[k]),
                        arrowprops=dict(arrowstyle="-|>",lw=1.7,color="#414e57",mutation_scale=13))
        ax.set_title(title,loc="left",color="#21323a",weight="bold",fontsize=15,pad=12)
        ax.grid(color="#dce2e2",linestyle=":",lw=.8)
        ax.set_axisbelow(True)
        ax.spines[["top","right"]].set_visible(False)
        ax.set(xlabel="Real part",ylabel="Imaginary part")
        ax.set_aspect("equal",adjustable="datalim")
        ax.margins(.08)
        shared_mark=(visit_marks if j==0 else other_marks)[j][0]
        ax.annotate("same position" if j==0 else "same reading",xy=shared_mark,
                    xytext=(14,-42) if j==0 else (18,-22),textcoords="offset points",
                    color=teal if j==0 else orange,weight="bold",fontsize=10,
                    arrowprops=dict(arrowstyle="-",color=teal if j==0 else orange))
    legend=[Line2D([],[],color=teal,marker="o",ms=8,ls="",label="Two visits with the same w"),
            Line2D([],[],color=orange,marker="D",ms=7,ls="",label="Two visits with the same A")]
    fig.legend(handles=legend,ncol=2,loc="lower center",bbox_to_anchor=(.5,.04),frameon=False,fontsize=11)
    fig.savefig(OUTPUT/"two-projections.png",dpi=175,bbox_inches="tight",pad_inches=.2)
    plt.close(fig)


if __name__=="__main__":
    draw()
