"""Render the figures used in chapters 4 and 5 from their archived measurements.

Run with Python 3 and Matplotlib: python tools/figures/proof-chapters.py
"""

import csv
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Rectangle


ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "archive"
FIGURES = ROOT / "docs" / "figures"
PAPER = "#fbfaf6"
INK = "#193642"
GRID = "#d4dcdb"
TEAL = "#087e79"
RUST = "#aa472a"
MUTED = "#546973"


def style():
    plt.rcParams.update({
        "figure.facecolor": PAPER, "axes.facecolor": PAPER, "font.family": "DejaVu Sans",
        "text.color": INK, "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK,
        "axes.edgecolor": GRID, "axes.spines.top": False, "axes.spines.right": False,
        "font.size": 12, "xtick.labelsize": 10.5, "ytick.labelsize": 11,
    })


def heading(fig, title, subtitle):
    fig.text(.075, .945, title, fontsize=20, fontweight="bold", va="top")
    fig.text(.075, .839, subtitle, fontsize=11.4, color=MUTED, va="top")


def save(fig, filename):
    FIGURES.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIGURES / filename, dpi=180, facecolor=PAPER)
    plt.close(fig)


def zero_positions():
    record = ARCHIVE / "2026-11-20-liu-angular-velocity-v002/windows.json"
    windows = json.loads(record.read_text(encoding="utf-8"))["windows"]
    fig, ax = plt.subplots(figsize=(12, 4.5))
    fig.subplots_adjust(left=.135, right=.955, top=.75, bottom=.21)
    heading(fig, "Eleven Riemann zeros in three Dottie windows",
            "Each circle marks one certified critical-line sign change. Each bar gives the full height window counted.")
    ax.axvline(0, linestyle="--", color="#788c8f", linewidth=1.2, zorder=1)
    for row in windows:
        multiple = row["multiple_of_T_D"]
        y = 4 - multiple
        side = float(Fraction(row["half_width"]))
        ax.add_patch(Rectangle((-side, y-.075), 2*side, .15, facecolor="#cbdedb", zorder=2))
        ax.vlines([-side, side], y-.15, y+.15, color="#648282", linewidth=1.5)
        brackets = row["hardy_brackets"]
        assert len(brackets) == row["zero_count"] == row["N_upper"] - row["N_lower"]
        right = -Fraction(row["half_width"])
        for item in brackets:
            lo, hi = map(Fraction, item["offsets"])
            assert right <= lo < hi <= Fraction(row["half_width"])
            assert item["signs"][0] * item["signs"][1] == -1
            right = hi
            ax.scatter(float((lo+hi)/2), y, s=100, color=TEAL, edgecolor=PAPER, linewidth=1.5, zorder=3)
    ax.set(yticks=[3,2,1], yticklabels=[r"$T_D$", r"$2T_D$", r"$3T_D$"],
           xticks=[-.5,-.25,0,.25,.5], xlim=(-.52,.52), ylim=(.5,3.52),
           xlabel=r"Height relative to each window center,  $t-kT_D$")
    ax.set_axisbelow(True)
    ax.grid(axis="x", color=GRID, alpha=.7)
    ax.spines["left"].set_visible(False)
    ax.tick_params(axis="y", length=0, pad=12, labelsize=14)
    fig.text(.075,.046,"All offsets share one scale. The certified sign brackets are narrower than the plotted circles.", fontsize=10, color=MUTED)
    save(fig, "proof-riemann-windows.png")


def proximity_controls():
    record = ARCHIVE / "2026-11-18-clock-proximity-results-v001/comparisons.csv"
    with record.open(encoding="utf-8", newline="") as file:
        rows = list(csv.DictReader(file))
    assert [int(row["j"]) for row in rows] == list(range(1,33))
    marks = {"win":("o",TEAL), "loss":("^",RUST), "unresolved":("x","#66717c")}
    counts = Counter(row[key] for row in rows for key in ("clock_vs_left","clock_vs_right"))
    fig, axes = plt.subplots(2,1,figsize=(12,5.4))
    fig.subplots_adjust(left=.20,right=.95,top=.71,bottom=.21,hspace=.81)
    heading(fig,"Which height was closer to a Riemann zero?",
            "For each of 32 inputs, I compared its Dottie height with one lower and one upper control height.")
    for panel, ax in enumerate(axes):
        section = rows[16*panel:16*(panel+1)]
        for i,row in enumerate(section):
            for y,key in [(1,"clock_vs_left"), (0,"clock_vs_right")]:
                marker,color=marks[row[key]]
                ax.scatter(i,y,marker=marker,s=95,color=color,linewidths=2,zorder=3)
        ax.set(xlim=(-.55,15.55), ylim=(-.35,1.35), yticks=[1,0],
               yticklabels=["Lower control","Upper control"],xticks=range(16),
               xticklabels=[r["j"] for r in section])
        ax.set_axisbelow(True)
        ax.grid(axis="x",color=GRID,linewidth=.8)
        ax.tick_params(length=0,pad=6)
        ax.spines["left"].set_visible(False)
        ax.spines["bottom"].set_visible(False)
    axes[1].set_xlabel("Input number in the published test", labelpad=8)
    labels={"win":"Dottie height closer","loss":"Control closer","unresolved":"Orbit unresolved"}
    entries=[Line2D([],[],marker=m,color=c,linestyle="none",markersize=9,
                    label=f"{labels[key]} ({counts[key]})") for key,(m,c) in marks.items()]
    fig.legend(handles=entries,loc="lower center",bbox_to_anchor=(.5,.015),ncol=3,frameon=False)
    save(fig,"proof-proximity-controls.png")


def hurwitz_transition():
    record = ARCHIVE / "2026-11-18-quartet-grid-comparison-v001/computations/global-quarter-shift-results.json"
    rows = json.loads(record.read_text(encoding="utf-8"))["finite_prefix"][:50]
    n = [row["n"] for row in rows]
    assert n == list(range(1,51))
    values = [float(row["Hurwitz_minus_one"].removeprefix("[").split()[0]) for row in rows]
    assert values[27] < 0 < values[28]
    # The comparison replaces only the radius by 2*pi*n.
    grid = []
    for level in n:
        B = math.comb(2*level,level)/4**level
        delta = level*(1-math.pi*level*B*B)
        grid.append(-1/12+delta/2-delta**2/2)
    fig, (whole, near) = plt.subplots(1,2,figsize=(12,5.2),gridspec_kw={"width_ratios":[1.25,1]})
    fig.subplots_adjust(left=.105,right=.955,top=.73,bottom=.21,wspace=.34)
    heading(fig,"The quartet radii change the sign between levels 28 and 29",
            "Both sequences use the same balanced-word factor. Only the quartet radii are replaced in the comparison grid.")
    for ax in (whole,near):
        ax.axhline(0,color=INK,linewidth=1.2,zorder=1)
        ax.set_axisbelow(True)
        ax.grid(axis="y",color=GRID,linewidth=.7,alpha=.8)
        ax.set_xlabel("Integer level  n")
    whole.scatter(n,grid,s=22,facecolors="none",edgecolors=RUST,linewidths=1.1,label=r"Grid radii  $2\pi n$")
    whole.scatter(n,values,s=17,color=TEAL,label=r"Quartet radii  $R_n$")
    whole.set(xlim=(0,51),xticks=[1,10,20,30,40,50],ylabel=r"Hurwitz value  $\zeta(-1,1-\delta_n)$",
              yticks=[-.02,-.01,0,.01],ylim=(-.022,.014))
    whole.legend(loc="lower right",frameon=True,framealpha=1,facecolor=PAPER,edgecolor="none",fontsize=10)
    near.scatter(n[25:32],values[25:32],s=55,color=TEAL,zorder=3)
    near.set(xlim=(25.6,32.4),xticks=list(range(26,33)),
             yticks=[-.0004,0,.0004,.0008],ylim=(-.00062,.00088))
    near.set_title("Quartet radii near the crossing",fontsize=12,pad=8)
    near.ticklabel_format(axis="y",style="sci",scilimits=(-3,-3),useMathText=True)
    near.annotate("28", xy=(28,values[27]),xytext=(-10,-20),textcoords="offset points",color=TEAL,fontweight="bold")
    near.annotate("29", xy=(29,values[28]),xytext=(0,11),textcoords="offset points",color=TEAL,fontweight="bold")
    fig.text(.075,.048,"Each point is an integer level. The horizontal line marks zero in both panels.",fontsize=10,color=MUTED)
    save(fig,"proof-hurwitz-crossing.png")


if __name__ == "__main__":
    style()
    zero_positions()
    proximity_controls()
    hurwitz_transition()
