"""Draw the reflected Gaussian input circles and their measured finite phases."""
import gzip
import io
import json
import math
import sys
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Circle
from PIL import Image

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "docs" / "figures"
SOURCE = ROOT / "archive" / "2026-11-20-gaussian-circle-phases-v001"
PAPER, INK, MUTED = "#fbf8f0", "#17313c", "#48606a"
RIGHT, LEFT, GRID = "#006b80", "#ac4826", "#d6dbd5"


def style_axes(ax):
    ax.set_facecolor(PAPER)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(labelsize=14, colors=INK, length=0, pad=6)


def circle_geometry():
    fig = plt.figure(figsize=(9.6, 5.5), facecolor=PAPER)
    fig.text(.095, .9, r"$w^*=1-\overline{w}$", color=INK, fontsize=22)
    fig.text(.89, .9, r"$T_0=T_D-1/512$", ha="right", color=INK, fontsize=19)
    ax = fig.add_axes([.105, .16, .83, .66])
    style_axes(ax)
    ax.set_aspect("equal")
    ax.set_xlim(-72, 72)
    ax.set_ylim(-39, 39)
    ax.set_xticks([-64, -32, 0, 32, 64])
    ax.set_yticks([-32, 0, 32])
    ax.axhline(0, color=GRID, lw=.9)
    ax.axvline(0, color=INK, lw=1.25, ls=(0, (3, 3)))
    ax.set_xlabel(r"$2048\,(\Re w-1/2)$", fontsize=17, color=INK)
    ax.set_ylabel(r"$2048\,(\Im w-T_0)$", fontsize=17, color=INK)
    for side, color in ((-1, LEFT), (1, RIGHT)):
        center = side * 32
        ax.add_patch(Circle((center, 0), 31, lw=2.7, ec=color, facecolor="none",
                            linestyle="--" if side == -1 else "-"))
        ax.scatter(center, 0, s=38, color=color, zorder=4)
        ax.text(center, -8, "$c^*$" if side == -1 else "$c$", ha="center", fontsize=17,
                color=color)
        a, b = math.pi/4, math.pi/4 + .38
        start = (center + side*31*math.cos(a), 31*math.sin(a))
        end = (center + side*31*math.cos(b), 31*math.sin(b))
        ax.scatter(*start, s=55, color=color, marker="D" if side == -1 else "o", zorder=5)
        ax.annotate("$w^*$" if side == -1 else "$w$", start, xytext=(4*side, 8),
                    textcoords="offset points", ha="center", color=color, fontsize=17)
        ax.annotate("", end, start, arrowprops=dict(arrowstyle="-|>", color=color, lw=2.3,
                                                   connectionstyle=f"arc3,rad={-.14*side}"))
    point_x = 32+31/math.sqrt(2)
    ax.plot([-point_x, point_x], [31/math.sqrt(2)]*2, color="#909990", lw=1.15, ls=":", zorder=0)
    ax.plot([32, 63], [0, 0], color=RIGHT, lw=1.35)
    ax.text(47, 2, "$31$", ha="center", color=RIGHT, fontsize=15)
    ax.text(0, 35, r"$\Re w=1/2$", ha="center", color=INK, fontsize=14, backgroundcolor=PAPER)
    fig.savefig(OUT / "gaussian-reflected-circles.png", dpi=160)
    plt.close(fig)


def load_replay():
    sys.dont_write_bytecode = True
    spec = spec_from_file_location("finite_phase", SOURCE / "replay.py")
    replay = module_from_spec(spec)
    spec.loader.exec_module(replay)
    return replay


def sampled_curves(replay, checkpoint, cutoff, count=384):
    arc, arb, acb = replay.arc, replay.arb, replay.acb
    arc.N = cutoff
    arc.mass = arb(checkpoint["mass"])
    arc.coeff_taylor = [acb(arb(x), arb(y)) for x, y in checkpoint["moments"]]
    arc.order = len(arc.coeff_taylor) - 1
    # Take midpoints for drawing. The archived interval test supplies the continuous bounds.
    x = [2*math.pi*j/count for j in range(count+1)]
    distances, roots = [], []
    for mirror in (False, True):
        values = []
        for j in range(count+1):
            z = replay.reading(replay.TAU*j/count, mirror)
            phase = z.arg() - replay.KAPPA*abs(z).log()
            values.append(math.remainder(float((phase - replay.TARGET).mid()), 2*math.pi))
        if mirror:
            for j, (a, b) in enumerate(zip(values, values[1:])):
                if a*b < 0 and abs(a-b) < math.pi:
                    lo, hi = x[j], x[j+1]
                    for _ in range(27):
                        mid = (lo + hi) / 2
                        z = replay.reading(arb(mid), True)
                        phase = z.arg() - replay.KAPPA*abs(z).log()
                        val = math.remainder(float((phase - replay.TARGET).mid()), 2*math.pi)
                        if val*a < 0:
                            hi = mid
                        else:
                            lo = mid
                    roots.append((lo+hi)/2)
        distances.append([abs(v) for v in values])
    assert len(roots) == 2
    return x, distances, roots


def frame(cutoff, x, distances, roots):
    fig = plt.figure(figsize=(9.6, 5.5), facecolor=PAPER)
    fig.text(.105, .905, r"$d_N(z)=\min_{k\in\mathbb{Z}}\,|\Phi_\kappa(L_N(z))-3.9+2\pi k|$",
             va="center", fontsize=17, color=INK)
    fig.text(.935, .905, f"$N={cutoff}$", va="center", ha="right", fontsize=16, color=INK)
    ax = fig.add_axes([.11, .20, .825, .60])
    style_axes(ax)
    ax.set(xlim=(0, 2*math.pi), ylim=(-.10, math.pi+.10))
    ax.set_xticks([0, math.pi/2, math.pi, 3*math.pi/2, 2*math.pi], ["0", "π/2", "π", "3π/2", "2π"])
    ax.set_yticks([0, .91, math.pi/2, math.pi], ["0", "0.91", "π/2", "π"])
    ax.grid(axis="y", color=GRID, lw=.7)
    ax.axhline(.91, color="#719394", lw=1.25, ls=":")
    ax.axhline(0, color=INK, lw=1)
    ax.plot(x, distances[0], lw=3.0, color=RIGHT, solid_capstyle="round")
    # Insert calculated cusp positions in the drawing so each reaches the zero-distance axis.
    left_curve = sorted(list(zip(x, distances[1])) + [(root, 0) for root in roots])
    xx, yy = zip(*left_curve)
    ax.plot(xx, yy, lw=2.5, ls="--", color=LEFT, dash_capstyle="round")
    ax.scatter(roots, [0, 0], marker="D", color=LEFT, ec=PAPER, lw=.95, s=58, zorder=4)
    ax.set_xlabel(r"$\theta$", fontsize=18, color=INK)
    ax.set_ylabel(r"$d_N$", fontsize=18, color=INK, rotation=0, labelpad=17)
    for pos, color, style, label in [(.12, RIGHT, "-", r"$d_N(w(\theta))$"),
                                      (.50, LEFT, "--", r"$d_N(w^*(\theta))$")]:
        fig.add_artist(Line2D([pos, pos+.062], [.055, .055], transform=fig.transFigure,
                              color=color, lw=2.9, ls=style))
        fig.text(pos+.080, .055, label, va="center", color=color, fontsize=16)
    return fig


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    circle_geometry()
    replay = load_replay()
    with gzip.open(SOURCE / "moments.json.gz", "rt") as stream:
        records = json.load(stream)["cutoffs"]
    cutoffs = sorted(map(int, records))[::8]
    assert len(cutoffs) == 25 and cutoffs[-1] == 2**28
    frames = []
    for cutoff in cutoffs:
        coords = sampled_curves(replay, records[str(cutoff)], cutoff)
        fig = frame(cutoff, *coords)
        if cutoff == cutoffs[-1]:
            fig.savefig(OUT / "gaussian-phase-cutoffs.png", dpi=160)
        stream = io.BytesIO()
        fig.savefig(stream, format="png", dpi=98)
        stream.seek(0)
        frames.append(Image.open(stream).convert("RGB"))
        plt.close(fig)
    durations = [1600] + [300]*(len(frames)-2) + [2100]
    frames[0].save(OUT / "gaussian-phase-cutoffs.gif", save_all=True, append_images=frames[1:],
                   duration=durations, loop=0, optimize=True)


if __name__ == "__main__":
    main()
