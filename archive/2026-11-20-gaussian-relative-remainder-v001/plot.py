"""Draw the measured relative motion for one signed Gaussian block."""
import gzip
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

from verify import PHASES, completed, phase


def main():
    with gzip.open(PHASES / "moments.json.gz", "rt") as stream:
        records = json.load(stream)["cutoffs"]
    before = completed(69206016, records["69206016"])
    after = completed(70254592, records["70254592"])
    angles = [phase.TAU * j / 1024 for j in range(1025)]
    curve = [after(t) / before(t) for t in angles]
    point = curve[4 * 139]
    x, y = float(point.real), float(point.imag)
    fig, ax = plt.subplots(figsize=(6.1, 5.1), layout="constrained")
    fig.patch.set_facecolor("#faf8f2")
    ax.set_facecolor("#faf8f2")
    ax.axvspan(0, 2.15, color="#e0f1eb")
    ax.add_patch(Circle((1, 0), 1, fill=False, edgecolor="#6b7481",
                        linewidth=1.5, linestyle="--"))
    ax.axvline(0, color="#373e44", lw=1.2)
    ax.axhline(0, color="#9baba8", lw=0.9)
    ax.plot([float(z.real) for z in curve], [float(z.imag) for z in curve],
            color="#00746d", lw=2.6)
    ax.annotate("", (x, y), (1, 0),
                arrowprops=dict(arrowstyle="->", lw=2, color="#b24e18"))
    ax.scatter([x], [y], color="#b24e18", marker="D", s=38, zorder=4)
    ax.scatter([0, 1], [0, 0], color="#223238", s=32, zorder=4)
    ax.annotate(r"$q=1$", (1, 0), xytext=(7, 9), textcoords="offset points")
    ax.annotate(r"$q=0$", (0, 0), xytext=(7, 9), textcoords="offset points")
    ax.annotate(r"$\theta=139\pi/128$", (x, y), xytext=(17, -19),
                textcoords="offset points", color="#8c3a12")
    ax.text(1.28, .94, r"$|q-1|=1$", color="#59626f", va="bottom")
    ax.set_aspect("equal")
    ax.set(xlim=(-.18, 2.15), ylim=(-1.28, 1.12),
           xlabel=r"$\mathrm{Re}\,q$", ylabel=r"$\mathrm{Im}\,q$")
    ax.spines[["right", "top"]].set_visible(False)
    fig.savefig(Path(__file__).with_name("gaussian-block.png"), dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    main()
