"""Draw the norm-73 prime pair and the two rooted words. Requires matplotlib and Pillow."""
import io
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Circle
from PIL import Image

OUT = Path(__file__).resolve().parents[2] / "docs" / "figures"
PAPER, INK, MUTED = "#fbf8f0", "#17313c", "#48606a"
BLUE, RUST, GRID = "#006b80", "#ac4826", "#d6dbd5"


def norm_pair():
    fig = plt.figure(figsize=(9.6, 5.5), facecolor=PAPER)
    ax = fig.add_axes([.085, .14, .49, .79], facecolor=PAPER, aspect="equal")
    ax.set(xlim=(-10.7, 10.7), ylim=(-10.7, 10.7),
           xticks=[-8, 0, 8], yticks=[-8, 0, 8])
    ax.set_xlabel(r"$\Re z$", fontsize=17, color=INK)
    ax.set_ylabel(r"$\Im z$", fontsize=17, color=INK)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(labelsize=13, colors=MUTED, length=0)
    ax.axhline(0, color=GRID)
    ax.axvline(0, color=GRID)
    ax.add_patch(Circle((0, 0), math.sqrt(73), fill=False, linestyle=(0, (3, 3)),
                        linewidth=1.8, edgecolor="#929c91"))
    for b, color, marker, label in [(8, RUST, "o", r"$3+8i$"), (-8, BLUE, "D", r"$3-8i$")]:
        ax.plot([0, 3], [0, b], color=color, linewidth=2.7)
        ax.scatter([3], [b], color=color, marker=marker, s=90, zorder=3)
        ax.annotate(label, (3, b), xytext=(9, 1 if b > 0 else -5),
                    textcoords="offset points", color=color, fontsize=17)
    ax.scatter(0, 0, s=22, color=INK, zorder=3)
    fig.text(.57, .84, r"$|z|^2=73$", size=23, color=INK)
    for y, color, gen, sign, residue in [
        (.65, RUST, "3+8i", "-1", 27),
        (.41, BLUE, "3-8i", "+1", 46),
    ]:
        fig.text(.57, y, rf"$\eta_\delta(({gen}))={sign}$", size=19, color=color)
        fig.text(.57, y-.080, rf"$i\equiv {residue}\;(\mathrm{{mod}}\;73)$", size=15, color=INK)
    fig.text(.57, .17, r"$a_{73}=(-1)+(+1)=0$", fontsize=19, color=INK)
    fig.savefig(OUT / "quartic-primes.png", dpi=160)
    plt.close(fig)


def word_frame(stage):
    fig = plt.figure(figsize=(9.6, 5.5), facecolor=PAPER)
    fig.text(.10, .88, r"$x_0=1,\qquad x_{k+1}=2^{\sigma_{k+1}x_k}$", fontsize=22, color=INK)
    fig.text(.91, .88, rf"$k={stage}$", ha="right", fontsize=20, color=INK)
    ax = fig.add_axes([.115, .22, .80, .59], facecolor=PAPER)
    ax.set_xlim(-.08, 2.13)
    ax.set_ylim(-2.35, 1.46)
    ax.set_xticks([0, 1, 2], labels=["0", "1", "2"])
    ax.set_yticks([-2, -1, 0, .5, 1], labels=[r"$1/4$", r"$1/2$", "$1$", r"$\sqrt{2}$", "$2$"])
    ax.grid(axis="y", color=GRID, lw=.8)
    ax.axhline(0, color="#899592", lw=1)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(length=0, labelsize=15, colors=INK, pad=6)
    ax.set_ylabel(r"$x_k$", fontsize=18, color=INK, rotation=0, labelpad=12)
    ax.set_xlabel(r"$k$", fontsize=18, color=INK)
    for values, color, marker, style in [
        ([0, -1, .5], RUST, "o", "-"), ([0, 1, -2], BLUE, "D", "--")
    ]:
        if stage:
            ax.plot(range(stage + 1), values[:stage + 1], color=color, lw=3.2,
                    ls=style, marker=marker, ms=9, mec=PAPER, mew=1.0)
    ax.scatter(0, 0, c=INK, s=80, zorder=4, edgecolor=PAPER)
    for x, color, label, style, marker in [
        (.13, RUST, r"$(\sigma_1,\sigma_2)=(-,+)$", "-", "o"),
        (.55, BLUE, r"$(\sigma_1,\sigma_2)=(+,-)$", "--", "D")
    ]:
        fig.add_artist(Line2D([x, x+.045], [.064, .064], transform=fig.transFigure,
                              color=color, lw=3, ls=style, marker=marker, markevery=[1], ms=6))
        fig.text(x+.063, .064, label, va="center", color=color, fontsize=15)
    return fig


def as_image(fig):
    stream = io.BytesIO()
    fig.savefig(stream, format="png", dpi=104)
    stream.seek(0)
    return Image.open(stream).convert("RGB")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    norm_pair()
    frames = []
    for stage in range(3):
        fig = word_frame(stage)
        frames.append(as_image(fig))
        if stage == 2:
            fig.savefig(OUT / "quartic-sign-orders.png", dpi=160)
        plt.close(fig)
    frames[0].save(OUT / "quartic-sign-orders.gif", save_all=True, append_images=frames[1:],
                   duration=[1250, 1700, 3100], loop=0, optimize=True)


if __name__ == "__main__":
    main()
