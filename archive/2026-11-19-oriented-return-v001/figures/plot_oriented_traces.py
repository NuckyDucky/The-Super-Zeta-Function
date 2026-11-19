"""Plot the exact first-trace curves and the two certified witness readings."""
import argparse
import json
from math import sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FormatStrFormatter


HERE = Path(__file__).resolve().parent
BLUE = "#005785"
ORANGE = "#ad5000"
INK = "#1d2930"


def midpoint(record):
    """Midpoint of a printed Arb ball, used only to draw its marker."""
    return float(record.lstrip("[").split()[0])


def draw(data, output):
    phases = json.loads(data.read_text(encoding="utf-8"))
    before, after = (midpoint(phases[key]["angle_deg"]) for key in ("original", "clockwise"))
    left, right = after - 2.2, before + 4.1
    # Both shifted determinant normalizations are regular on this angle range.
    assert -120 < left < after < -90 < before < right < -60
    theta = np.linspace(left, right, 1200)
    fig, ax = plt.subplots(figsize=(8.8, 4.55))
    fig.subplots_adjust(left=.095, right=.982, bottom=.17, top=.77)
    fig.text(.095, .940, "The two spectral readings exchange order at −90°",
             color=INK, fontsize=17, weight="bold", va="center")
    for sign, color, style, marker, key in [
        (1, BLUE, "-", "o", "trace_plus"),
        (-1, ORANGE, (0, (5, 2.6)), "s", "trace_minus"),
    ]:
        label = (r"$M_+$   at $\theta+30^\circ$" if sign == 1
                 else r"$M_-$   at $\theta-30^\circ$")
        curve = 2 / (1 - np.sin(np.deg2rad(theta + sign * 30)))
        ax.plot(theta, curve, color=color, linestyle=style, linewidth=2, label=label)
        for phase, angle in [("clockwise", after), ("original", before)]:
            y = midpoint(phases[phase][key])
            ax.scatter(angle, y, marker=marker, s=43, facecolor=color, edgecolor="white",
                       linewidth=1, zorder=5)
            if phase == "clockwise":
                xytext = (8, 7)
            else:
                xytext = (6, 9 if sign == 1 else -12)
            ax.annotate(f"{y:.4f}", (angle, y), xytext=xytext, textcoords="offset points",
                        color=color, va="center", fontsize=10, weight="bold",
                        bbox=dict(facecolor="white", edgecolor="none", alpha=.86, pad=.6))

    for angle, label in [(after, "After the turn"), (before, "Original witness")]:
        ax.axvline(angle, color="#a6b0b5", linewidth=.8, linestyle=(0, (2, 3)), zorder=0)
        ax.text(angle, 1.018, label, transform=ax.get_xaxis_transform(), color=INK,
                fontsize=9.5, ha="left" if angle == after else "center", va="bottom")
    arrow_y = 1.289
    ax.annotate("", xy=(after + 3.4, arrow_y), xytext=(before - 2, arrow_y),
                arrowprops=dict(arrowstyle="->", color=INK, linewidth=.95, shrinkA=0, shrinkB=0))
    ax.text((after + before) / 2, arrow_y, "30° clockwise", va="center", ha="center",
            color=INK, fontsize=9.5, bbox=dict(facecolor="white", edgecolor="none", pad=3))
    pivot = 8 - 4 * sqrt(3)
    ax.scatter(-90, pivot, marker="D", s=34, facecolor="white", edgecolor=INK,
               linewidth=1.2, zorder=6)
    ax.annotate(r"$M_+=M_-=8-4\sqrt{3}$", xy=(-90, pivot), xytext=(-96.5, 1.173),
                ha="center", color=INK, fontsize=10.5,
                arrowprops=dict(arrowstyle="-", color=INK, linewidth=.8, shrinkB=6))
    ax.set(xlim=(left, right), ylim=(.982, 1.32), ylabel="First reciprocal-root sum",
           xlabel=r"Native return angle $\theta$ (degrees)")
    xticks = [after, -110, -100, -90, before]
    tick_labels = [f"{x:.2f}" if x in (before, after) else f"{x:d}" for x in xticks]
    ax.set_xticks(xticks, labels=[label.replace("-", "−") for label in tick_labels])
    ax.set_yticks([1, 1.05, 1.10, 1.15, 1.20, 1.25, 1.30])
    ax.yaxis.set_major_formatter(FormatStrFormatter("%.2f"))
    ax.set_axisbelow(True)
    ax.grid(axis="y", color="#e2e7e9", linewidth=.65)
    ax.spines[["top", "right"]].set_visible(False)
    for spine in ("left", "bottom"):
        ax.spines[spine].set_color("#78858b")
    ax.tick_params(colors=INK, labelsize=9, length=3)
    ax.xaxis.label.set_color(INK)
    ax.yaxis.label.set_color(INK)
    ax.legend(loc="upper left", bbox_to_anchor=(.092, .892), bbox_transform=fig.transFigure,
              ncol=2, frameon=False, borderaxespad=0, columnspacing=2.6,
              handlelength=2.7, fontsize=10)
    fig.savefig(output, dpi=240, facecolor="white",
                metadata={"Title": "Ordered spectral traces of the period-640 Dottie witness"})
    plt.close(fig)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--data", type=Path, default=HERE.parent / "data" / "quarter_probe.json")
    cli.add_argument("--output", type=Path, default=HERE / "oriented-traces.png")
    args = cli.parse_args()
    draw(args.data, args.output)
