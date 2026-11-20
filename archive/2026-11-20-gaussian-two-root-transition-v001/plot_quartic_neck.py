"""Draw the inverse solutions on the boundaries of three quartic sublevel sets."""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D

folder = Path(__file__).resolve().parent
record = json.loads((folder/"quartic-neck.json").read_text())
quartic = json.loads((folder/"quartic-first-tube.json").read_text())
def mid(key):
    return float(key.strip("[]").split()[0])

level, c = mid(record["r_star"]), mid(record["c"])
x,y = np.meshgrid(np.linspace(-.041,.041,620),np.linspace(-.062,.062,670))
values = np.abs(np.polynomial.polynomial.polyval(c+x+1j*y,quartic["ascending_coefficients"]))
fig,axes=plt.subplots(1,3,figsize=(9.4,5.3))
fig.subplots_adjust(left=.085,right=.97,top=.78,bottom=.24,wspace=.20)
ink="#193741"; teal="#278389"; gold="#bd541d"
fig.text(.06,.92,"What moves as the quartic neck opens?",fontsize=20,color=ink,weight="bold")
fig.text(.06,.85,"The outline is |P(z)| = v. On that outline, orange marks the two inputs giving the positive real value v.",fontsize=10.7,color=ink)
for ax,ratio,title in zip(axes,("0.75","1","1.25"),("Approach from above and below","Meet at the critical point","Separate to the left and right")):
    r=float(ratio)*level
    ax.contourf(x,y,values,levels=[-1,r],colors=["#e5f3f3"])
    ax.contour(x,y,values,levels=[r],colors=[teal],linewidths=1.5)
    ax.axhline(0,color="#aebfc2",lw=.7,zorder=0)
    ax.set_aspect("equal"); ax.set_title(title,fontsize=9.8,color=ink,pad=9)
    ax.spines[["right","top"]].set_visible(False)
    ax.tick_params(length=2,labelsize=8)
    ax.set_xticks([-.03,0,.03]); ax.set_yticks([-.04,0,.04])
    if ax is axes[0]: ax.set_ylabel("Imaginary part of z",fontsize=9)
    else: ax.tick_params(labelleft=False)
    ax.set_xlabel(f"v = {ratio} × merger level",fontsize=9)
    m = mid(record["cases"]["0"]["midpoint"])-c
    b=mid(record["y"])
    ax.scatter([m,m],[-b,b],s=27,color=ink,zorder=3)
    entry=record["cases"][ratio]
    m=mid(entry["midpoint"])-c
    gap=0j if ratio=="1" else complex(mid(entry["signed_squared_separation"]))**.5/2
    pts=np.array([m+gap,m-gap])
    ax.plot(pts.real,pts.imag,ls="--",lw=1.2,color=gold)
    ax.scatter(pts.real,pts.imag,s=43,marker="D",color=gold,zorder=4)
handles=[Line2D([],[],color=ink,marker="o",linestyle="",label="Fixed roots of P(z) = 0"),
         Line2D([],[],color=gold,marker="D",linestyle="",label="Moving solutions of P(z) = v")]
fig.legend(handles=handles,loc="lower center",bbox_to_anchor=(.5,.065),ncol=2,frameon=False,fontsize=10)
fig.text(.06,.038,"Horizontal position is Re z − 1.399144801. The horizontal dashed segment at right measures the width of the neck.",fontsize=9.5,color=ink)
fig.savefig(folder/"quartic-neck-readings.png",dpi=200)
