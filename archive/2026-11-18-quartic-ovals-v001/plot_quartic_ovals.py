"""Plot the two real branches and their projective completion."""
import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np


PAPER = "#f8fafc"
INK = "#17283c"
MUTED = "#475569"
GUIDE = "#c8d4df"
UPPER = "#125eb2"
LOWER = "#95601c"
MARK = "#9c2764"
AT_INFINITY = np.sqrt(961000)


def ordinate(x, z):
    """Return the positive normalized square root in homogeneous coordinates."""
    numerator = 465*x*x - 183*x*z - 659*z*z
    denominator = 155*x*x + 396*x*z - 936*z*z
    return np.hypot(numerator - denominator, 2*numerator) / AT_INFINITY


def radial_coordinates(theta, sign):
    height = ordinate(np.sin(theta/2), np.cos(theta/2))
    radius = 2 + sign*(1 + height)/2
    return radius*np.cos(theta), radius*np.sin(theta)


def main(output):
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "mathtext.fontset": "stix",
        "axes.labelcolor": INK,
        "xtick.color": MUTED,
        "ytick.color": MUTED,
    })
    fig = plt.figure(figsize=(12.4, 5.7), facecolor=PAPER)
    layout = fig.add_gridspec(1, 2, left=.085, right=.975, top=.765, bottom=.20,
                             width_ratios=(1.04, 1), wspace=.22)
    affine = fig.add_subplot(layout[0], facecolor=PAPER)
    complete = fig.add_subplot(layout[1], facecolor=PAPER)
    fig.text(.085, .908, "Two real ovals of the quartic",
             fontsize=23, fontweight="bold", color=INK)

    x = np.linspace(-4.7, 5.1, 1800)
    scale = np.hypot(x, 1)
    y = ordinate(x/scale, 1/scale)
    x_e = np.e
    scale_e = np.hypot(x_e, 1)
    y_e = ordinate(x_e/scale_e, 1/scale_e)
    for sign, color in ((1, UPPER), (-1, LOWER)):
        affine.axhline(sign, color=GUIDE, lw=1, linestyle=(0, (4, 4)), zorder=0)
        affine.plot(x, sign*y, color=color, lw=2.1)
    affine.axvline(x_e, color=MARK, alpha=.35, linestyle=(0, (3, 4)), lw=1)
    affine.scatter([x_e], [y_e], s=60, color=MARK, edgecolor=PAPER, linewidth=1.2, zorder=5)
    affine.annotate(r"$x=e$", (x_e, y_e), xytext=(x_e+.30, 1.37), color=MARK, fontsize=13,
                    arrowprops={"arrowstyle": "-", "color": MARK, "lw": 1.3})
    affine.set(
        xlim=(-4.7, 5.1),
        ylim=(-1.57, 1.57),
        xticks=(-4, -2, 0, 2, 4),
        yticks=(-1, 0, 1),
        xlabel=r"Input $x$",
        ylabel=r"Normalized ordinate $\widetilde Y$",
    )
    affine.tick_params(labelsize=12, color=GUIDE)
    affine.xaxis.label.set_size(13)
    affine.yaxis.label.set_size(13)
    affine.set_title("Affine branches", loc="left", fontsize=15, color=INK,
                     fontweight="bold", pad=13)
    for side in ("top", "right"):
        affine.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        affine.spines[side].set_color(GUIDE)

    theta = np.linspace(-np.pi, np.pi, 2401)
    complete.plot(2*np.cos(theta), 2*np.sin(theta), color=GUIDE,
                  linestyle=(0, (4, 4)), lw=1)
    complete.plot((-3.16, 0), (0, 0), color=GUIDE, linestyle=(0, (3, 4)), lw=1)
    for sign, color in ((1, UPPER), (-1, LOWER)):
        xp, yp = radial_coordinates(theta, sign)
        complete.plot(xp, yp, color=color, lw=2.8)
        complete.scatter([-2-sign], [0], s=38, color=PAPER, edgecolor=color,
                         linewidth=1.6, zorder=4)
    xe, ye = radial_coordinates(2*np.arctan(x_e), 1)
    complete.scatter([xe], [ye], s=60, color=MARK, edgecolor=PAPER, linewidth=1.2, zorder=5)
    complete.annotate(r"$x=e$", (xe, ye), xytext=(-3.32, 2.25), color=MARK, fontsize=13,
                      arrowprops={"arrowstyle": "-", "color": MARK, "lw": 1.3})
    complete.annotate(r"$x=\infty$", (-3, 0), xytext=(-3.83, -.66), color=MUTED,
                      fontsize=13, arrowprops={"arrowstyle": "-", "color": MUTED, "lw": 1})
    complete.set(xlim=(-3.85, 3.48), ylim=(-3.05, 3.05), aspect="equal")
    complete.set_title("Projective completion", loc="left", fontsize=15, color=INK,
                       fontweight="bold", pad=13)
    complete.set_axis_off()

    handles = [
        plt.Line2D([0], [0], color=UPPER, lw=3, label="Upper branch"),
        plt.Line2D([0], [0], color=LOWER, lw=3, label="Lower branch"),
        plt.Line2D([0], [0], color=MARK, marker="o", linestyle="None", markersize=7,
                   label=r"Upper point giving $\widehat\pi$"),
    ]
    fig.legend(handles=handles, loc="lower left", bbox_to_anchor=(.079, .035),
               ncols=3, frameon=False, fontsize=12, labelcolor=INK)
    fig.savefig(output, dpi=220, facecolor=PAPER)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    main(parser.parse_args().output)
