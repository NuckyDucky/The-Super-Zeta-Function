"""Replay the Dottie spectral map and interactive companion into a scratch directory."""
import argparse
import base64
import io
import json
from pathlib import Path
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.colors as colors
import matplotlib.pyplot as plt
import numpy as np


repo_here = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, default=repo_here, help="Super Zeta checkout containing the root verifier")
parser.add_argument("--output", type=Path, required=True, help="Scratch directory outside the preserved archive")
args = parser.parse_args()
archive = (args.repo.resolve() / "archive").resolve()
source_archive = Path(__file__).resolve().parents[1]
args.output = args.output.resolve()
if args.output.is_relative_to(archive) or args.output.is_relative_to(source_archive):
    parser.error("--output must be outside the preserved archive")
verifier = archive / "2026-11-20-hurwitz-speed-mean-square-v001"
if not (verifier / "verify_two_inputs.py").is_file():
    parser.error("--repo must contain the archived two-input verifier")

sys.dont_write_bytecode = True
sys.path.insert(0, str(verifier))
from verify_two_inputs import ROOT_COUNT, PRECISION, ctx, determinant_roots

args.output.mkdir(parents=True, exist_ok=True)

ctx.prec = PRECISION
d, roots = determinant_roots(ROOT_COUNT)
radii = np.array([float(abs(lam)) for lam in roots])
angles = np.array([float(lam.arg()) for lam in roots])
logs = np.log(radii)
m = 301
edge = np.pi/3
joint = np.linspace(-2*edge,2*edge,2*m-1)
waves = np.exp(-1j*np.outer(joint,logs))*(2/radii**2)
growth = 2*np.sinh(np.outer(joint,angles)/2)**2
field = growth @ waves.T
i, j = np.ogrid[:m,:m]
pixels = np.abs(field[i+j, j-i+m-1])

fig = plt.figure(figsize=(8.4,7.2),dpi=180,facecolor="white")
ax = fig.add_axes([.145,.19,.66,.66])
bar = fig.add_axes([.847,.31,.022,.43])
palette = colors.LinearSegmentedColormap.from_list("angle",["#f7f6ef","#e5d6a4","#dba35d","#b56851","#713e57","#362a48"])
limit = np.ceil(pixels.max()/.02)*.02
img=ax.imshow(pixels,origin="lower",extent=(-edge,edge,-edge,edge),cmap=palette,vmin=0,vmax=limit,interpolation="bilinear",aspect="equal")
ax.plot([-edge,edge],[edge,-edge],color="#66615d",ls=(0,(2,4)),lw=1)
alpha=np.pi/6
for x,y,label in [(alpha,alpha,"++"),(alpha,-alpha,"+−"),(-alpha,alpha,"−+"),(-alpha,-alpha,"−−")]:
    ax.plot(x,y,"o",ms=4.2,mfc="white",mec="#202431",mew=1.2)
    ax.annotate(label,(x,y),xytext=(6,5),textcoords="offset points",color="#202431",fontsize=10,weight="semibold",
                bbox=dict(facecolor="white",edgecolor="none",alpha=.85,pad=1))
ticks=[-edge,-alpha,0,alpha,edge]
labs=[r"$-\pi/3$",r"$-\pi/6$","0",r"$\pi/6$",r"$\pi/3$"]
ax.set(xticks=ticks,yticks=ticks,xticklabels=labs,yticklabels=labs,xlabel=r"First imaginary shift $h$ in $x=1+ih$",ylabel=r"Second imaginary shift $k$ in $y=1+ik$")
ax.tick_params(length=3,color="#656674",labelsize=10)
ax.xaxis.labelpad=8
ax.yaxis.labelpad=7
for spine in ax.spines.values():
    spine.set_color("#8d9295")
fig.text(.087,.947,"How much do the quartet angles contribute?",fontsize=20,color="#282336",weight="semibold")
fig.text(.087,.895,"Two independent imaginary inputs to the Dottie spectral sum",fontsize=12,color="#47444c")
cb=fig.colorbar(img,cax=bar)
cb.set_ticks(np.arange(0,limit+.001,.04))
cb.ax.tick_params(labelsize=9,length=2)
cb.set_label("Change in the complex sum (magnitude)",fontsize=9,labelpad=8)
cb.outline.set_edgecolor("#9d9ba0")
fig.text(.087,.082,r"At each point, compare the full sum with the reading at the same $h-k$ and with $h+k=0$.",fontsize=10,color="#35323b")
fig.text(.087,.045,r"Along the dotted line $k=-h$, the root angles cancel exactly. The full sum can still be complex.",fontsize=10,color="#35323b")
fig.canvas.draw()
axpos=ax.get_position()
buf=io.BytesIO()
fig.savefig(buf,format="png",dpi=180,facecolor="white")
png=buf.getvalue()
(args.output/"two-input-dottie-map.png").write_bytes(png)
plt.close(fig)

html = Path(__file__).with_name("map-template.html").read_text(encoding="utf-8")
position = [100*axpos.x0,100*(1-axpos.y1),100*axpos.width,100*axpos.height]
payload=[2*np.log(float(d)),np.column_stack((logs,angles)).tolist()]
html=html.replace("@IMAGE@",base64.b64encode(png).decode()).replace("@DATA@",json.dumps(payload,separators=(",",":"))).replace("@POS@",json.dumps(position))
(args.output/"two-input-dottie-map.html").write_text(html,encoding="utf-8")
print(f"{m} by {m} samples; maximum plotted change {pixels.max():.8f}; absolute omitted tail of change < {4*np.exp(2*edge*np.pi)/(3*np.pi**4*(ROOT_COUNT-.5)**3):.3g}.")
