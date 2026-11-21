"""Draw the continued Hurwitz roots and their three passes from archived coordinates."""
import json
from fractions import Fraction
from math import pi, radians
from pathlib import Path
from flint import arb

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "archive"
OUTPUT = ROOT / "docs/figures"
PAPER, GRID, INK = "#fbf8f0", "#d3dedb", "#17313c"
COLORS = ["#006b80", "#ac4826", "#6d4a88"]


def canvas():
    fig, axes = plt.subplots(1, 2, figsize=(10.4, 4.4), layout="constrained")
    for ax in axes:
        ax.set_facecolor(PAPER)
        ax.set_axisbelow(True)
        ax.grid(axis="y", color=GRID, linewidth=.7)
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["left", "bottom"]].set_color(GRID)
        ax.tick_params(colors=INK, labelsize=11, length=3)
    return fig, axes


def save(fig, name):
    OUTPUT.mkdir(exist_ok=True, parents=True)
    fig.savefig(OUTPUT / name, dpi=150, facecolor=PAPER)
    plt.close(fig)


def midpoint(ball):
    return float(arb(ball).mid())


def successors():
    source = ARCHIVE / "2026-11-19-zero-transport-v001/Dottie-Forward-Iteration"
    fig, (plane, sweep) = canvas()
    plane.axvline(.5, color=INK, linestyle="--", linewidth=1)
    sweep.axhline(.5, color=INK, linestyle="--", linewidth=1)
    labels = [r"$\rho_3\to\rho_4$", r"$\rho_4\to b$", r"$b\to\rho_7$"]
    for j, (color, label) in enumerate(zip(COLORS, labels), 1):
        samples = json.loads((source / f"sweep_{j}.json").read_bytes())["checkpoints"]
        x = [midpoint(p["zero"]["real"]) for p in samples]
        y = [midpoint(p["zero"]["imag"]) for p in samples]
        angles = [pi*(.5-float(Fraction(p["shift"]))) for p in samples]
        assert abs(angles[0]-pi/3)<1e-12 and abs(angles[-1]-pi/4)<1e-12
        for ax, xx, yy in [(plane,x,y), (sweep,angles,x)]:
            ax.plot(xx, yy, color=color, lw=2.2, label=label)
            ax.annotate("", (xx[150], yy[150]), (xx[142], yy[142]),
                        arrowprops={"arrowstyle":"-|>", "color":color, "lw":1.6})
        plane.scatter([x[0],x[-1]], [y[0],y[-1]], s=27, color=PAPER, edgecolors=color, zorder=3)
        if j == 1:
            plane.annotate(r"$\rho_3$", (x[0],y[0]), (7,-1), textcoords="offset points")
        end = [r"$\rho_4$",r"$b$",r"$\rho_7$"][j-1]
        plane.annotate(end,(x[-1],y[-1]),(5,3),textcoords="offset points")
    plane.set(xlabel=r"$\Re\,w$",ylabel=r"$\Im\,w$", xlim=(-.35,1.05))
    sweep.set(xlabel=r"$\theta$", ylabel=r"$\Re\,w$",xlim=(pi/3+.005,pi/4-.005),ylim=(-.28,1.12))
    sweep.set_xticks([pi/3, 5*pi/16, 7*pi/24, 13*pi/48, pi/4],
                     [r"$\pi/3$",r"$5\pi/16$",r"$7\pi/24$",r"$13\pi/48$",r"$\pi/4$"])
    sweep.legend(ncol=3,fontsize=11,frameon=False,loc="upper left",handlelength=1.3,
                 columnspacing=1.2,handletextpad=.4)
    save(fig,"proof-successor-paths.png")


def passes():
    source = ARCHIVE / "2026-11-19-sixth-passes-v001/compute"
    data = json.loads((source/"jets.json").read_bytes())
    rows = data["profiles"]
    events = [r["mid"] for r in data["events"]]
    fig, (plane, sweep) = canvas()
    plane.plot([row[1] for row in rows], [row[2] for row in rows], color=INK, lw=2)
    plane.axhline(37.25, color=INK, lw=1, ls="--")
    sweep.axhline(0, color=INK, lw=1, ls="--")
    sweep.axvline(0, color=INK, lw=.8, ls=":")
    for j,(p,color,marker) in enumerate(zip(events[::2],COLORS,["o","s","^"]),1):
        assert p["T"] == 37.25
        plane.scatter(p["sigma"], p["T"], s=42, color=color, marker=marker, zorder=4)
        offsets = [(2,9),(-10,-18),(3,9)]
        plane.annotate(str(j), (p["sigma"],p["T"]), offsets[j-1], textcoords="offset points",color=color)
        near = [row for row in rows if abs(row[0]-p["alpha"])<=.25]
        sweep.plot([radians(row[0]-p["alpha"]) for row in near],
                   [row[2]-37.25 for row in near], color=color, lw=2.4, label=str(j))
    for p in events[1::2]:
        plane.scatter(p["sigma"],p["T"],s=28,color=INK,marker="D",zorder=3)
    revisit = json.loads((source/"revisit.json").read_bytes())["mid"]
    plane.scatter(revisit["sigma"],revisit["T"],s=78,facecolors="none",edgecolors=INK,marker="s")
    plane.set(xlabel=r"$\Re\,w$",ylabel=r"$\Im\,w$")
    sweep.set(xlabel=r"$h-h_j$",ylabel=r"$\Im\,w-37.25$",ylim=(-.071,.071))
    sweep.legend(ncol=3,frameon=False, loc="upper center",handlelength=1.6)
    for ax in (plane,sweep):
        ax.yaxis.set_major_locator(MaxNLocator(5))
    save(fig,"proof-sixth-passes.png")


if __name__ == "__main__":
    successors()
    passes()
