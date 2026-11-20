"""Plot the six exact normalized derivatives. Requires Python 3.10+ and matplotlib."""
from itertools import accumulate, permutations
from math import pi
from operator import mul
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def normalized_derivative(word):
    prefix_products = accumulate((1 if sign == "+" else -1 for sign in word), mul)
    return -sum(c * (-1j * pi) ** j for j, c in enumerate(prefix_products, 1))


def main():
    ink = "#183548"
    muted = "#4a6471"
    marker = "#086c77"
    grid = "#dbe3e6"
    plt.rcParams.update({"font.family": "DejaVu Sans", "mathtext.fontset": "dejavusans"})
    fig, ax = plt.subplots(figsize=(6.2, 5.9))
    fig.subplots_adjust(left=0.23, right=0.95, bottom=0.20, top=0.76)
    fig.text(0.065, 0.94, "The six second derivatives at the cap",
             fontsize=18, color=ink, fontweight="bold")
    fig.text(0.065, 0.865, r"Each word has $W(1)=-1$ and $W'(1)=\pi^4$ at $L=\pi i$."
             "\n" + r"The points give $K=W''(1)/W'(1)$ in the complex plane.",
             fontsize=11.2, color=ink, linespacing=1.45)

    ax.set_xlim(-119, -75.5)
    ax.set_ylim(-42, 42)
    ax.set_xticks([-pi**4-pi**2, -pi**4+pi**2],
                  [r"$-\pi^4-\pi^2$", r"$-\pi^4+\pi^2$"])
    ax.set_yticks([-pi**3-pi, -pi**3+pi, 0, pi**3-pi, pi**3+pi],
                  [r"$-\pi^3-\pi$", r"$-\pi^3+\pi$", "0",
                   r"$\pi^3-\pi$", r"$\pi^3+\pi$"])
    ax.set_xlabel(r"Real part of $K$", fontsize=12.5, color=ink, labelpad=10)
    ax.set_ylabel(r"Imaginary part of $K$", fontsize=12.5, color=ink, labelpad=8)
    ax.tick_params(axis="both", length=0, colors=muted, labelsize=11, pad=6)
    ax.grid(color=grid, linewidth=0.8)
    for side, spine in ax.spines.items():
        spine.set_visible(side in ("bottom", "left"))
        spine.set_color("#9cadaf")
    for letters in sorted(set(permutations("++--"))):
        word = "".join(letters)
        value = normalized_derivative(word)
        ax.scatter(value.real, value.imag, s=57, facecolor=marker,
                   edgecolor="white", linewidth=0.8, zorder=3)
        ax.annotate(word, xy=(value.real, value.imag), xytext=(8, 0),
                    textcoords="offset points", va="center",
                    fontfamily="DejaVu Sans Mono", fontsize=13, fontweight="bold",
                    color=ink, bbox={"facecolor": "white", "edgecolor": "none", "pad": 1})
    fig.text(0.065, 0.056, "Read each word left to right from the same starting cap.",
             fontsize=10.5, color=muted)
    fig.savefig(Path(__file__).with_name("derivative-words.png"), dpi=260,
                facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    main()
