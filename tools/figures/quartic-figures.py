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


def page(title, subtitle):
    fig = plt.figure(figsize=(9.6, 5.85), facecolor=PAPER)
    fig.text(.062, .94, title, va="top", fontsize=23, color=INK, family="DejaVu Serif")
    fig.text(.064, .84, subtitle, va="top", fontsize=13, color=MUTED)
    return fig


def norm_pair():
    fig = page("One norm, two Gaussian primes",
               "The two dots are generators above the rational prime 73.")
    ax = fig.add_axes([.08, .15, .42, .61], facecolor=PAPER, aspect="equal")
    ax.set(xlim=(-10, 10), ylim=(-10, 10), xticks=[-8, 0, 8], yticks=[-8, 0, 8],
           xlabel="Real part", ylabel="Imaginary part")
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(labelsize=11, colors=MUTED, length=0)
    ax.axhline(0, color=GRID)
    ax.axvline(0, color=GRID)
    ax.add_patch(Circle((0, 0), math.sqrt(73), fill=False, linestyle=(0, (3, 3)),
                        linewidth=1.5, edgecolor="#929c91"))
    for b, color, label in [(8, RUST, "3 + 8i"), (-8, BLUE, "3 − 8i")]:
        ax.plot([0, 3], [0, b], color=color, linewidth=2.4)
        ax.scatter([3], [b], color=color, s=65, zorder=3)
        ax.annotate(label, (3, b), xytext=(8, 1 if b > 0 else -5),
                    textcoords="offset points", color=color, weight="bold", fontsize=12)
    ax.scatter(0, 0, s=18, color=INK, zorder=3)
    for y, color, gen, sign, detail in [
        (.68, RUST, "3 + 8i", "−1", "i ≡ 27 (mod 73)"),
        (.49, BLUE, "3 − 8i", "+1", "i ≡ 46 (mod 73)"),
    ]:
        fig.text(.54, y, gen + "   →   " + sign, size=20, weight="bold", color=color)
        fig.text(.54, y-.06, detail, size=14, color=INK)
    fig.text(.54, .28, "Gaussian coefficient at norm 73", fontsize=14, color=MUTED)
    fig.text(.54, .20, "(−1) + (+1) = 0", fontsize=19, color=INK)
    fig.text(.063, .040, "Dashed circle:  Re(z)² + Im(z)² = 73.   Each sign is the quartic character at that ideal.",
             fontsize=11, color=MUTED)
    fig.savefig(OUT / "quartic-primes.png", dpi=160)
    plt.close(fig)


def word_frame(stage):
    fig = page("The order of two exponential stages",
               "Both words start at 1. Each stage applies either 2ˣ or 2⁻ˣ to the preceding value.")
    ax = fig.add_axes([.12, .18, .77, .51], facecolor=PAPER)
    ax.set_xlim(-.15, 2.25)
    ax.set_ylim(-2.32, 1.42)
    ax.set_xticks([0, 1, 2], labels=["Cap", "First stage", "Second stage"])
    ax.set_yticks([-2, -1, 0, .5, 1], labels=["¼", "½", "1", "√2", "2"])
    ax.grid(axis="y", color=GRID, lw=.8)
    ax.axhline(0, color="#899592", lw=1)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(length=0, labelsize=13, colors=INK, pad=6)
    ax.set_ylabel("Value on a log₂ scale", fontsize=12, color=MUTED)
    for word, values, color, marker, style in [
        ("−+", [0, -1, .5], RUST, "o", "-"), ("+−", [0, 1, -2], BLUE, "D", "--")
    ]:
        if stage:
            ax.plot(range(stage + 1), values[:stage + 1], color=color, lw=2.8,
                    ls=style, marker=marker, ms=8, mec=PAPER, mew=1.1)
    ax.scatter(0, 0, c=INK, s=70, zorder=4, edgecolor=PAPER)
    for x, color, label, style in ((.12, RUST, "− then +", "-"), (.44, BLUE, "+ then −", "--")):
        fig.add_artist(Line2D([x, x+.045], [.745, .745], transform=fig.transFigure,
                              color=color, lw=3, ls=style))
        fig.text(x+.055, .745, label, va="center", color=color, fontsize=15, weight="bold")
    sentence = ["The cap is the input shared by both words.",
                "The first signs send 1 to ½ and 2.",
                "The second signs give 2 raised to ½ = √2 and 2 raised to −2 = ¼."][stage]
    fig.text(.064, .052, sentence, fontsize=13, color=INK)
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
