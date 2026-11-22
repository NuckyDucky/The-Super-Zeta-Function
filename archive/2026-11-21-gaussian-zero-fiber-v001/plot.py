"""Draw the three traces. Pass an optional output PNG filename."""
from pathlib import Path
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import mpmath as mp
import numpy as np

# The figure samples both traces. The two root markers use the certified bracket.
snapshot = Path(__file__).resolve().parent
prior = snapshot.parent / "2026-11-21-gaussian-pinch-v001"
sys.path.insert(0, str(prior))
from central_detours import END, N, denominator_data
from flint import ctx
import json

ctx.prec = 96
scale, bins, _, last = denominator_data(snapshot.parents[1])
nodes, gauss_weights = np.polynomial.legendre.leggauss(160)
x = (nodes + 1) * END / 2
u = np.exp(x) / float(scale)
# Approximate each positive Abel bin at its weighted-mean norm for the figure.
means = [lo + moment / mass for lo, _, mass, moment in bins]
masses = [mass for _, _, mass, _ in bins]
theta = -np.expm1(-u) * (np.exp(-np.outer(u, means)) @ masses) + last * np.exp(-N * u)
weights = END * gauss_weights * np.exp(x/2) * theta
heights = np.linspace(0, 0.30, 151)
values = (np.cos(np.outer(heights, x)) @ weights) / weights.sum()
record = json.loads((prior / "central-detours.json").read_text(encoding="utf-8"))
lower, upper_bound = map(float, record["refinement"]["height_bracket"])
root = (lower + upper_bound) / 2
warm = "#b75220"
cool = "#226aab"
ink = "#142d3b"
muted = "#53707a"
pale = "#d6e1e2"
mp.mp.dps = 24
# Logarithmic Mellin integral in y=log(u). The verified endpoint enclosure
# is computed independently in check_images.py. This grid draws the trace.
mesh = np.linspace(-80., 9., 4451)
dx = mesh[1] - mesh[0]
v = np.exp(mesh)
weight = np.exp(-mesh/4)*np.log1p(v/np.cosh(np.sqrt(v))**2)
def phi(t):
    s = complex(.25, t/2)
    integral = dx*np.sum(weight*np.exp(-.5j*t*mesh))
    j = s*np.sin(np.pi*s)/np.pi*integral
    return j + 2*np.pi**(-2*s)*(2**(2*s)-1)*complex(mp.zeta(2*s))

ts = np.unique(np.r_[np.linspace(0, .30, 161), root])
zs = np.array([phi(t) for t in ts])
upper = phi(root)
assert -.35481 < upper.real < -.35339 and -.47364 < upper.imag < -.47217
plt.rcParams.update({"font.family":"DejaVu Sans","mathtext.fontset":"dejavusans",
    "font.size":12,"text.color":ink,"axes.labelcolor":ink,
    "xtick.color":muted,"ytick.color":muted,"axes.edgecolor":pale,
    "axes.spines.top":False,"axes.spines.right":False,"savefig.facecolor":"#ffffff"})
fig, ax = plt.subplots(1, 3, figsize=(12.5,4.9), width_ratios=[.85,1.18,1.55])
fig.subplots_adjust(left=.066,right=.985,bottom=.20,top=.83,wspace=.40)
fig.patch.set_facecolor("white")
for a in ax:
    a.tick_params(length=3, width=.8)
    a.grid(False)
def title(a, formula):
    a.set_title(formula, fontsize=16, loc="left", pad=15)
def mark(a, x,y, color, marker):
    a.scatter(x,y,s=70,marker=marker,facecolor=color,edgecolor="white",linewidth=1.3,zorder=6)
def base_marker(a,x,y):
    a.scatter(x,y,s=26,facecolor="white",edgecolor=muted,linewidth=1.25,zorder=4)
u,g,p=ax
title(u,r"$w=\frac{1}{2}+it$")
u.set_xlim(.43,.57); u.set_xticks([.45,.50,.55]); u.set_xlabel(r"$\operatorname{Re}\,w$")
u.set_ylabel(r"$t=\operatorname{Im}\,w$")
u.axvline(.5,color=muted,ls=(0,(3,4)),lw=1.0)
u.axhline(0,color=pale,lw=1)
for a in [u,g]:
    a.set_ylim(-.31,.31); a.set_yticks([-.25,0,.25])
mark(u,.5,root,warm,"o"); mark(u,.5,-root,cool,"D")
u.annotate(r"$w_+$",(.5,root),xytext=(10,1),textcoords="offset points",color=warm)
u.annotate(r"$w_-$",(.5,-root),xytext=(10,-4),textcoords="offset points",color=cool)
title(g,r"$\Lambda(w)/\Lambda(\frac{1}{2})$")
g.set_xlim(-.17,1.08); g.set_xticks([0,.5,1.0]); g.set_xlabel(r"$\operatorname{Re}\,\Lambda(w)/\Lambda(\frac{1}{2})$")
g.set_ylabel(r"$t$")
g.axvline(0,color=muted,lw=1,ls=(0,(3,4)))
g.axhline(0,color=pale,lw=1)
mask=heights<=.3
g.plot(values[mask],heights[mask],color=warm,lw=2.2)
g.plot(values[mask],-heights[mask],color=cool,lw=2.2)
mark(g,0,root,warm,"o"); mark(g,0,-root,cool,"D")
base_marker(g,1,0)
title(p,r"$\Phi(w)=\mathcal{Z}(w/2\,;1)$")
p.set_xlim(-.67,-.15); p.set_ylim(-.60,.60)
p.set_xticks([-.6,-.4,-.2]); p.set_yticks([-.5,0,.5]); p.set_xlabel(r"$\operatorname{Re}\,\Phi$"); p.set_ylabel(r"$\operatorname{Im}\,\Phi$")
p.axhline(0,color=pale,lw=1)
p.plot(zs.real,zs.imag,color=warm,lw=2.2)
p.plot(zs.real,-zs.imag,color=cool,lw=2.2)
base_marker(p,zs[0].real,0)
mark(p,upper.real,upper.imag,warm,"o"); mark(p,upper.real,-upper.imag,cool,"D")
p.annotate(r"$\Phi(w_+)$",(upper.real,upper.imag),xytext=(-13,-13),textcoords="offset points",ha="right",color=warm)
p.annotate(r"$\Phi(w_-)$",(upper.real,-upper.imag),xytext=(-13,9),textcoords="offset points",ha="right",color=cool)
fig.legend(handles=[Line2D([],[],color=warm,marker="o",lw=2,label=r"Counterclockwise detour  $(+\pi)$"),
                    Line2D([],[],color=cool,marker="D",lw=2,label=r"Clockwise detour  $(-\pi)$")],
           frameon=False,ncol=2,loc="lower center",bbox_to_anchor=(.5,-.005),fontsize=11)
out = Path(sys.argv[1]) if len(sys.argv) == 2 else Path("gaussian-zero-fiber.png")
fig.savefig(out,dpi=180)
print(out)
