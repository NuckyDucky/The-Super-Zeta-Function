"""Plot the two certified clockwise reference-zero continuations.
Run in the same directory as the two arithmetic_braid_*.json records.
"""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from flint import arb

base = Path(__file__).resolve().parent

def points(seed):
    data = json.loads((base / f"arithmetic_braid_{seed}.json").read_text())["paths"][0]
    return [(float(arb(p["zero"]["real"]).mid()), float(arb(p["zero"]["imag"]).mid()))
            for p in data["checkpoints"]]

fig, ax = plt.subplots(figsize=(8.7, 6.5), layout="constrained")
ax.spines[["top", "right"]].set_visible(False)
ax.grid(axis="y", color="#e4e8e9")
ax.axvline(0.5, color="#849298", linestyle="--", lw=1.1)
ax.text(.49, 11.30, "Critical line", color="#596973", fontsize=10, ha="right")
colors = ["#007568", "#76428b"]
for seed, color, label in zip(["lattice", "riemann"], colors,
    ["Start at the factor zero", "Start at the Riemann zero"]):
    path = points(seed)
    x, y = zip(*path)
    ax.plot(x, y, color=color, lw=2.7, label=label, zorder=3)
    for k in (70,185):
        ax.annotate("", xy=path[k+6], xytext=path[k-4],
                    arrowprops=dict(arrowstyle="-|>", color=color, lw=2.4, mutation_scale=15))
    ax.scatter([x[0], x[-1]],[y[0], y[-1]], s=44, color=color, zorder=4)
ax.scatter([.5], [14.13472514173469], s=63, edgecolor="#1f2937", color="white", zorder=5)
interior = json.loads((base/"fifth_residue.json").read_text())["paths"]
for index, (seed,color) in enumerate(zip(("lattice","riemann"),colors)):
    zero = interior[seed]["zero"]
    ax.scatter(float(arb(zero["real"]).mid()),float(arb(zero["imag"]).mid()),s=45,
               facecolor="white",edgecolor="#27343d",marker="D",zorder=6,
               label="54° on each path" if index==0 else None)
ax.annotate(r"$4\pi i/\log 3$ at $60^\circ$", xy=points("lattice")[0],
            xytext=(12,-1), textcoords="offset points", va="center", fontsize=11)
ax.annotate(r"$4\pi i/\log 2$ at $45^\circ$", xy=points("riemann")[-1],
            xytext=(12,1), textcoords="offset points", va="center", fontsize=11)
ax.annotate(r"$\rho_1$" + "\n" + "arrival at 45°\ndeparture at 60°",
            xy=(.5,14.13472514173469), xytext=(-100,5), textcoords="offset points",
            fontsize=10.5, va="center", arrowprops=dict(arrowstyle="-",color="#777"))
ax.set_xlim(-.035,.65)
ax.set_ylim(10.85,18.9)
ax.set_xlabel(r"Real part of $w$", fontsize=12)
ax.set_ylabel(r"Imaginary part of $w$", fontsize=12)
ax.set_title("Two zero paths through the first Riemann zero", loc="left", fontsize=17, pad=12, weight="semibold")
ax.legend(loc="upper right", frameon=True, facecolor="white", framealpha=1,
          edgecolor="none", fontsize=10)
fig.savefig(base/"zero-paths.png", dpi=200, facecolor="white")
