"""Plot input-coordinate enclosures for two real target families of the Gaussian factor."""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, NullFormatter


FOLDER = Path(__file__).resolve().parent


def plot(positions_path, corridor_path, output):
    positions = json.loads(positions_path.read_text(encoding="utf-8"))
    corridor = json.loads(corridor_path.read_text(encoding="utf-8"))
    cases = {case["sign"]: case for case in corridor["corridors"]}
    core_edge = float(Fraction(corridor["core_real_input_bounds"][1]))
    small = max(float(case["small_endpoint_magnitude"]) for case in cases.values())
    large = min(float(case["large_endpoint_magnitude"]) for case in cases.values())
    ticks = [large, 1e-16, 1e-17, small]
    tick_labels = [r"$6\times10^{-16}$", r"$10^{-16}$", r"$10^{-17}$", r"$1.05238\times10^{-18}$"]
    ink = "#1B3441"
    muted = "#425963"
    excluded = "#D8E4E6"
    fig, axes = plt.subplots(1, 2, sharex=True, sharey=True, figsize=(10.8, 6.0))
    fig.subplots_adjust(left=0.088, right=0.945, bottom=0.295, top=0.74, wspace=0.22)
    fig.text(.055, .937, "Where the Gaussian factor takes a signed real value",
             fontsize=20, fontweight="bold", color=ink)
    fig.text(.055, .871, r"Right-hand solution of $f(w)=y$ in the Dottie window "
             r"$|\mathrm{Im}\,w-T_D|<1/16$.  Each marker is the center of a certified disk.",
             fontsize=11.5, color=muted)

    for ax, (sign, title, marker, color) in zip(axes, (
        (1, "Positive target", "o", "#076E70"),
        (-1, "Negative target", "D", "#9C452E"),
    )):
        case = cases[sign]
        assert case["preimages"] == 2 and case["distinct_simple"]
        ax.set_xscale("log")
        ax.set_xlim(large * 1.3, small / 1.3)
        ax.set_ylim(1.0, 1.215)
        ax.fill_between([small, large], 1, core_edge, color=excluded, linewidth=0)
        ax.plot([small, large], [core_edge, core_edge], lw=1, color="#607B81")
        for row in positions["positions"]:
            y = float(row["target"])
            if sign*y > 0 and row["certified"]:
                ax.errorbar(abs(y), row["center_re"], yerr=float(Fraction(row["radius"])),
                            fmt=marker, markersize=5.5, capsize=4.5, elinewidth=1.5,
                            markeredgewidth=1.25, color=color, zorder=3)
        ax.set_title(title, loc="left", pad=7, fontsize=13, fontweight="bold", color=color)
        ax.xaxis.set_major_locator(FixedLocator(ticks))
        ax.set_xticklabels(tick_labels, fontsize=9, color=ink)
        ax.xaxis.set_minor_formatter(NullFormatter())
        ax.set_yticks([1.018, 1.05, 1.10, 1.15, 1.20],
                      labels=["1.018", "1.05", "1.10", "1.15", "1.20"])
        ax.tick_params(axis="x", which="minor", length=0)
        ax.tick_params(axis="both", which="major", labelcolor=ink, color="#74828A", length=3)
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["bottom", "left"]].set_color("#9BA9AC")
        ax.grid(axis="y", color="#DFE6E8", lw=.65)
        ax.set_axisbelow(True)
    axes[0].set_ylabel(r"Real part of the input, $\sigma=\mathrm{Re}\,w$", fontsize=11, color=ink)
    fig.text(.51, .199, r"Target magnitude $|y|$ on a log scale, decreasing toward zero  $\longrightarrow$",
             ha="center", fontsize=11, color=ink)
    fig.text(.055, .111, "Bars project each disk onto the real axis (center ± radius). "
             "The disk encloses one solution at that target.", fontsize=10.3, color=muted)
    fig.text(.055, .052, r"Both signs stay above the shaded band ($\sigma>1.018$) "
             r"for every magnitude between the end ticks. The zero count at $y=0$ remains open.",
             fontsize=10.3, color=muted)
    fig.savefig(output, dpi=200, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--positions", type=Path, default=FOLDER / "branch-positions.json")
    parser.add_argument("--corridor", type=Path, default=FOLDER / "gaussian-target-corridor.json")
    parser.add_argument("--output", type=Path, default=FOLDER / "gaussian-branch-positions.png")
    args = parser.parse_args()
    plot(args.positions, args.corridor, args.output)
