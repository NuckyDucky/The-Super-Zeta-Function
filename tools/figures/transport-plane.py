"""Draw the atlas maps in the complex plane from the archived numerical transport."""
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "archive/2026-11-19-dottie-plane-atlas-v001/atlas"
OUT = ROOT / "docs/figures"
sys.dont_write_bytecode = True
sys.path.insert(0, str(ATLAS))
from plane_map import fields, rk
from two_paths import follow

INK, MUTED, PAPER, GRID = "#17313c", "#48606a", "#fbf8f0", "#d6dbd5"
ROWS = ("#a34b26", "#007383", "#80659c", "#536e88")


def axes(fig, bounds, xlabel, ylabel):
    ax = fig.add_axes(bounds, facecolor=PAPER, aspect="equal")
    ax.spines[["top", "right"]].set_visible(False)
    for edge in ("left", "bottom"):
        ax.spines[edge].set_color("#9da89d")
    ax.grid(color=GRID, linewidth=.75)
    ax.set_axisbelow(True)
    ax.tick_params(labelsize=12, colors=MUTED, length=0, pad=6)
    ax.set_xlabel(xlabel, color=INK, fontsize=17)
    ax.set_ylabel(ylabel, color=INK, fontsize=17)
    return ax


def arrow(ax, points, i, j, color):
    a, b = points[i], points[j]
    ax.annotate("", xy=(b.real, b.imag), xytext=(a.real, a.imag),
                arrowprops=dict(arrowstyle="-|>", mutation_scale=12, color=color,
                                linewidth=1.5, shrinkA=0, shrinkB=0))


def transport_path(zero, h0):
    cols, rows = [12, 44, 76, 108], [8, 32, 56, 80]
    indices = np.ix_(rows, cols)
    with np.load(ATLAS / "plane_map.npz", allow_pickle=False) as data:
        x, y = data["x"][cols], data["y"][rows]
        assert data["accepted"][indices].all()
        expected = data["end"][indices].flatten()
    starts = (x[None, :] + 1j*y[:, None]).flatten()
    paths, slope = rk(starts, h0, 384)
    coarse, _ = rk(starts, h0, 192)
    assert np.all(slope > 1e-4) and np.max(abs(paths[::2] - coarse)) < 2e-5
    assert np.max(abs(paths[-1] - expected)) < 2e-5
    levels = fields(starts, 1/6 + h0/180)[0]
    for angle, points in zip(np.linspace(h0, 15, len(paths)), paths):
        values = fields(points, 1/6 + angle/180)[0]
        assert np.all(abs(values - levels)/(1 + abs(levels)) < 5e-7)

    fig = plt.figure(figsize=(8.5, 6.4), facecolor=PAPER)
    ax = axes(fig, [.088, .105, .59, .825], r"$\Re w$", r"$\Im w$")
    ax.set(xlim=(-.73, 1.07), ylim=(36.34, 38.55), xticks=[-.5, 0, .5, 1],
           yticks=[36.5, 37, 37.5, 38, 38.5])
    for k, path in enumerate(paths.T):
        color = ROWS[k // len(x)]
        ax.plot(path.real, path.imag, lw=1.45, color=color)
        arrow(ax, path, 121, 151, color)
        ax.plot(path[0].real, path[0].imag, "o", mec=color, mfc=PAPER, mew=1.6, ms=5)
        ax.plot(path[-1].real, path[-1].imag, "D", mec=color, mfc=color, ms=4)
    ax.plot(zero.real, zero.imag, color=PAPER, lw=6, zorder=5)
    ax.plot(zero.real, zero.imag, color=INK, lw=2.8, zorder=6)
    ax.plot(zero[0].real, zero[0].imag, "o", mec=INK, mfc=PAPER, mew=1.8, ms=8, zorder=7)
    ax.plot(zero[-1].real, zero[-1].imag, "*", mec=PAPER, mfc=INK, mew=.7, ms=18, zorder=7)
    ax.annotate(r"$\rho_6$", (zero[-1].real, zero[-1].imag), xytext=(8, -8),
                textcoords="offset points", color=INK, fontsize=15, zorder=8)
    fig.text(.685, .84, r"$H(w,b)=c$", fontsize=20, color=INK)
    fig.text(.685, .72, r"$\Im w(h_0)$", fontsize=17, color=MUTED)
    for i, (height, color) in enumerate(zip(y, ROWS)):
        yy = .65 - .059*i
        fig.add_artist(Line2D([.686, .739], [yy, yy], color=color, lw=2.4, transform=fig.transFigure))
        fig.text(.753, yy, f"{height:.2f}", va="center", fontsize=15, color=color)
    for yy, marker, fill, label in [
            (.325, "o", PAPER, r"$w(h_0)$"),
            (.245, "D", MUTED, r"$w(\pi/12)$"),
            (.165, "*", INK, r"$\rho_6$")]:
        fig.add_artist(Line2D([.706], [yy], marker=marker, mfc=fill, mec=INK, ms=10 if marker=="*" else 7,
                              linestyle="none", transform=fig.transFigure))
        fig.text(.748, yy, label, va="center", color=INK, fontsize=15)
    fig.savefig(OUT / "proof-complex-turn.png", dpi=180)
    plt.close(fig)


def offset_path(angles, delta):
    fig = plt.figure(figsize=(8.5, 6.4), facecolor=PAPER)
    fig.text(.115, .91, r"$\Delta=10^6(w_1-w_0)$", color=INK, fontsize=21)
    ax = axes(fig, [.14, .12, .77, .72], r"$\Re\Delta$", r"$\Im\Delta$")
    ax.set(xlim=(-.15,1.31), ylim=(-.13,1.13), xticks=[0,.25,.5,.75,1,1.25], yticks=[0,.25,.5,.75,1])
    ax.axhline(0, color=MUTED, lw=1)
    ax.axvline(0, color=MUTED, lw=1)
    t = np.linspace(-.28, 1.78, 240)
    ax.plot(np.cos(t), np.sin(t), color="#8c978e", linestyle=(0, (2.5, 3)), lw=1.7)
    ax.annotate(r"$|\Delta|=1$", (.75,.66), xytext=(-9,16), textcoords="offset points",
                color=MUTED, fontsize=14)
    ax.plot(delta.real, delta.imag, color=ROWS[1], lw=2.9)
    arrow(ax, delta, 46, 66, ROWS[1])
    arrow(ax, delta, 235, 253, ROWS[1])
    ax.scatter(0, 0, s=38, color=INK)
    ax.plot([0,delta[-1].real], [0,delta[-1].imag], color="#9ba79e", lw=.9)
    for j, mark, label, offset, ha in [
        (0, "o", r"$h_0$", (-4,-14), "right"),
        (int(np.abs(angles-14.30).argmin()), "o", r"$h\approx0.2496$", (11,-1), "left"),
        (-1, "D", r"$h=\pi/12$", (-9,-15), "left")]:
        z = delta[j]
        ax.plot(z.real, z.imag, mark, mec=ROWS[1], mfc=PAPER if j==0 else ROWS[1],
                mew=1.8, ms=6.5, zorder=4)
        ax.annotate(label, (z.real,z.imag), xytext=offset, textcoords="offset points",
                    color=INK, ha=ha, fontsize=13)
    fig.savefig(OUT / "proof-complex-offset.png", dpi=180)
    plt.close(fig)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    _, records = follow(320)
    angles, zero, nearby, gap = (np.asarray(col) for col in zip(*records))
    delta = (nearby-zero)*1e6
    assert np.max(abs(abs(delta)-gap)) < 1e-8
    assert abs(delta[0]-1) < 1e-8 and abs(delta[-1]-(.247208976+.905975071j)) < 1e-8
    transport_path(zero, angles[0])
    offset_path(angles, delta)


if __name__ == "__main__":
    main()
