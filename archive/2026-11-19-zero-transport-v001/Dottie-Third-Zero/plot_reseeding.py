"""Draw the recorded paths of the clockwise Hurwitz reference sweeps."""

import json
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from flint import arb


HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "Dottie-Off-Axis-Return"
PREVIOUS = HERE.parent / "Dottie-Second-Zero"
INK = "#172c3c"
GREY = "#8795a1"
COLORS = ["#00695e", "#ae4b18", "#664099", "#24559d", "#993956", "#394839"]


def read_path(filename):
    data = json.loads(filename.read_text(encoding="utf-8"))
    rows = (data.get("paths") or [data])[0]["checkpoints"]
    points = []
    for row in rows:
        shift = Fraction(row.get("b") or row["shift"])
        real, imag = (float(arb(row["zero"][key]).mid()) for key in ("real", "imag"))
        points.append((90 - 180 * float(shift), real, imag))
    return points


def draw_path(ax, points, i, j, color, fresh=True):
    zorder = 3 if fresh else 2
    width = 2.8 if fresh else 2
    ax.plot([p[i] for p in points], [p[j] for p in points],
            color=color, lw=width, zorder=zorder, solid_capstyle="round")
    k = len(points) * 2 // 3
    h = max(1, len(points) // 70)
    ax.annotate("", xy=(points[k+h][i], points[k+h][j]),
                xytext=(points[k-h][i], points[k-h][j]),
                arrowprops=dict(arrowstyle="-|>", color=color, lw=1.7,
                                shrinkA=0, shrinkB=0, mutation_scale=13))


def dot(ax, x, y, color):
    ax.scatter(x, y, facecolor="white", edgecolor=color,
               linewidth=1.7, s=43, zorder=5)


def label(ax, x, y, text, color, offset):
    ax.annotate(text, xy=(x, y), xytext=offset, textcoords="offset points",
                fontsize=11.3, color=color, ha="right" if offset[0] < 0 else "left",
                va="center", zorder=6)


def make_figure(end_labels):
    history = [
        read_path(OLD / "arithmetic_braid_lattice.json"),
        read_path(OLD / "arithmetic_braid_riemann.json"),
        read_path(PREVIOUS / "dyadic_continuation.json"),
    ]
    sweeps = [read_path(HERE / f"sweep_{i+1}.json") for i in range(len(end_labels))]
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 11, "text.color": INK,
        "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK,
        "axes.edgecolor": "#7c8b95", "axes.spines.top": False,
        "axes.spines.right": False, "axes.labelpad": 8, "axes.axisbelow": True,
    })
    fig, (plane, angle) = plt.subplots(1, 2, figsize=(13.3, 6.7))
    fig.subplots_adjust(left=.073, right=.97, bottom=.16, top=.79, wspace=.24)
    fig.suptitle("One clockwise turn from the second Riemann zero to the third",
                 x=.073, y=.96, ha="left", fontsize=23, weight="bold")
    fig.text(.073, .88, "Each sweep starts at 60° and ends at 45°. At a reset, the zero keeps its complex address.",
             fontsize=12.5)
    for ax, title in ((plane, "The path in the complex plane"), (angle, "The moving reference zero crosses the line")):
        ax.set_title(title, loc="left", fontweight="bold", fontsize=14, pad=12)
        ax.grid(axis="y", color="#e0e6ea", linewidth=.8)
    plane.axvline(.5, color="#687983", lw=1.2, ls=(0,(4,3)))
    angle.axhline(.5, color="#687983", lw=1.2, ls=(0,(4,3)))
    for i, pts in enumerate(history):
        draw_path(plane, pts, 1, 2, GREY, False)
        dot(plane, *pts[0][1:], GREY)
        text = [r"$4\pi i/\log 3$", r"$\rho_1$", r"$4\pi i/\log 2$"][i]
        label(plane, *pts[0][1:], text, "#4c6170", [(8,-9),(9,5),(9,9)][i])
    label(plane, *sweeps[0][0][1:], r"$\rho_2$", INK, (9,0))
    for i, (pts, end) in enumerate(zip(sweeps, end_labels)):
        color = COLORS[i]
        draw_path(plane, pts, 1, 2, color)
        draw_path(angle, pts, 0, 1, color)
        dot(plane, *pts[0][1:], color)
        dot(plane, *pts[-1][1:], color)
        dot(angle, *pts[0][:2], color)
        dot(angle, *pts[-1][:2], color)
        if end:
            label(plane, *pts[-1][1:], end, color, (8,9))
    # Locate the interior crossing on the drawn polyline; rigorous enclosures
    # for any enunciated numerical estimates are separately calculated.
    for p, q in zip(sweeps[0][1:-2], sweeps[0][2:-1]):
        if p[1] < .5 < q[1]:
            fraction = (.5 - p[1]) / (q[1] - p[1])
            cross = p[0] + fraction * (q[0] - p[0])
            angle.annotate("Interior crossing", xy=(cross,.5), xytext=(-15,30),
                           textcoords="offset points", ha="right", color=INK, fontsize=10.5,
                           arrowprops=dict(arrowstyle="->", color="#738591", lw=1.1))
            break
    label(angle, *sweeps[0][0][:2], r"Start at $\rho_2$", INK, (5,12))
    label(angle, *sweeps[-1][-1][:2], r"Land at $\rho_3$", INK, (-4,-14))
    plane.set(xlabel=r"Real part of $w$", ylabel=r"Height, $\mathrm{Im}\,w$")
    plane.margins(x=.22,y=.065)
    angle.set(xlabel="Clockwise turn angle (degrees)", ylabel=r"Real part of moving zero",
              xlim=(60.35,44.65), xticks=[60,57,54,51,48,45])
    angle.margins(y=.13)
    fig.text(.073, .027, "Grey paths precede the frozen test. Arrows follow increasing sweep time. Dashed lines mark Re(w) = ½.",
             fontsize=10.3, color="#4a5e6b")
    fig.savefig(HERE / "reseeding-paths.png", dpi=200, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    make_figure([r"$\rho_3$"])
