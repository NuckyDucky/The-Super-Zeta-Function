"""Plot the error in NuckyDucky's original six-integer approximation."""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator
import mpmath as mp


def target(x):
    return (1 + x) * (2 + x) / (x**2 + x - 1)


def plot(output):
    mp.mp.dps = 85
    n = 465 * mp.e**2 - 183 * mp.e - 659
    d = 155 * mp.e**2 + 396 * mp.e - 936
    pi_hat = (3 * d - n + mp.sqrt((n - d)**2 + 4 * n**2)) / (2 * (n - d))
    scale = mp.mpf("1e20")
    displacement = (pi_hat - mp.pi) * scale
    gap = (n / d - target(mp.pi)) * scale
    assert mp.mpf("8.682007272724") < -displacement < mp.mpf("8.682007272726")
    assert mp.mpf("2.6231439430444") < gap < mp.mpf("2.6231439430445")
    offsets = [mp.mpf(k) / 20 for k in range(-296, 127)]
    values = [(target(mp.pi + dx / scale) - target(mp.pi)) * scale for dx in offsets]

    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 13,
                         "mathtext.fontset": "dejavuserif", "text.color": "#18263b",
                         "axes.labelcolor": "#18263b", "axes.edgecolor": "#9caabc"})
    fig, ax = plt.subplots(figsize=(10.8, 5.65), dpi=220, layout="constrained")
    ax.plot(list(map(float, offsets)), list(map(float, values)), color="#235e99", lw=2.6,
            label=r"$10^{20}\,[T(x)-T(\pi)]$")
    ax.axhline(float(gap), color="#a54116", lw=1.7, linestyle="--",
               label=r"$10^{20}\,[R(e)-T(\pi)]$")
    ax.axhline(0, color="#8c99aa", lw=1)
    ax.vlines(float(displacement), 0, float(gap), color="#a54116", lw=1.2, linestyle=":")
    ax.scatter([float(displacement), 0], [float(gap), 0], c=["#a54116", "#235e99"],
               edgecolor="white", linewidth=1.2, s=92, zorder=4)
    ax.annotate(r"$\widehat{\pi}$", (float(displacement), float(gap)), xytext=(8, 12),
                textcoords="offset points", color="#8b3714", fontsize=16)
    ax.annotate(r"$\pi$", (0, 0), xytext=(8, 10), textcoords="offset points",
                color="#235e99", fontsize=16)
    ax.annotate("", xy=(0, -1.28), xytext=(float(displacement), -1.28),
                arrowprops={"arrowstyle": "<->", "color": "#35465e", "lw": 1.2})
    ax.text(float(displacement) / 2, -1.07, r"$\pi-\widehat{\pi}\approx 8.6820\times10^{-20}$",
            ha="center", va="bottom", fontsize=13)
    ax.set(xlabel=r"Horizontal displacement $10^{20}(x-\pi)$",
           ylabel=r"Vertical displacement from $T(\pi)$ (units of $10^{-20}$)",
           xlim=(-15, 6.3), ylim=(-2, 4.85))
    ax.xaxis.set_major_locator(MultipleLocator(3))
    ax.yaxis.set_major_locator(MultipleLocator(1))
    ax.grid(color="#d9e0e9", linewidth=0.65)
    ax.set_axisbelow(True)
    ax.set_title(r"The quadratic reconstruction of $\pi$", loc="left", fontsize=21, pad=12)
    ax.legend(loc="upper right", frameon=True, facecolor="white", framealpha=0.96)
    ax.spines[["top", "right"]].set_visible(False)
    fig.savefig(output, facecolor="white",
                metadata={"Title": "The quadratic reconstruction of pi",
                          "Author": "Original approximation: NuckyDucky"})
    plt.close(fig)
    print(f"pi-hat = {mp.nstr(pi_hat, 52)}")
    print(f"pi - pi-hat = {mp.nstr(-displacement / scale, 30)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="PNG output filename")
    plot(parser.parse_args().output)
