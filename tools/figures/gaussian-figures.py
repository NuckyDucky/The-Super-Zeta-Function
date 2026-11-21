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


def fig_page(title, subtitle):
    fig = plt.figure(figsize=(9.6, 5.85), facecolor=PAPER)
    fig.text(.062, .94, title, va="top", fontsize=23, color=INK, family="DejaVu Serif")
    fig.text(.064, .84, subtitle, va="top", fontsize=13, color=MUTED)
    return fig


def style_axes(ax):
    ax.set_facecolor(PAPER)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.tick_params(labelsize=11, colors=INK, length=0, pad=6)


def circle_geometry():
    fig = fig_page("Two circles at the Dottie height", "Each input on the right has a partner at the same height on the left.")
    ax = fig.add_axes([.10, .20, .82, .52])
    style_axes(ax)
    ax.set_aspect("equal")
    ax.set_xlim(-72, 72)
    ax.set_ylim(-40, 40)
    ax.set_xticks([-64, -32, 0, 32, 64])
    ax.set_yticks([-32, 0, 32])
    ax.axhline(0, color=GRID, lw=.9)
    ax.axvline(0, color=INK, lw=1.25, ls=(0, (3, 3)))
    ax.set_xlabel("Real displacement from ½  (units of 1/2048)", fontsize=12, color=INK)
    ax.set_ylabel("Height above T₀\n(units of 1/2048)", fontsize=12, color=INK)
    for side, color in ((-1, LEFT), (1, RIGHT)):
        center = side * 32
        ax.add_patch(Circle((center, 0), 31, lw=2.4, ec=color, facecolor="none",
                            linestyle="--" if side == -1 else "-"))
        ax.scatter(center, 0, s=32, color=color, zorder=4)
        ax.text(center, -7, "left" if side == -1 else "right", ha="center", fontsize=13,
                color=color, weight="bold")
        a, b = math.pi/4, math.pi/4 + .38
        start = (center + side*31*math.cos(a), 31*math.sin(a))
        end = (center + side*31*math.cos(b), 31*math.sin(b))
        ax.scatter(*start, s=35, color=color, marker="D" if side == -1 else "o", zorder=5)
        ax.annotate("", end, start, arrowprops=dict(arrowstyle="-|>", color=color, lw=2.3,
                                                   connectionstyle=f"arc3,rad={-.14*side}"))
    point_x = 32+31/math.sqrt(2)
    ax.plot([-point_x, point_x], [31/math.sqrt(2)]*2, color="#909990", lw=1, ls=":", zorder=0)
    ax.text(0, 38, "critical line", ha="center", color=INK, fontsize=11, backgroundcolor=PAPER)
    fig.text(.064, .07, "Both radii are 31/2048. Each inner edge lies 1/2048 from the critical line.",
             color=INK, fontsize=13)
    fig.text(.064, .023, "T₀ = Tᴅ − 1/512. Arrows show increasing input angle on the right and its reflection.",
             color=MUTED, fontsize=11)
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
    fig = fig_page("A phase missed on the right circle",
                   "Distance from the chosen phase of 3.9 radians, measured on both reflected circles.")
    for pos, color, style, label in [(0.10, RIGHT, "-", "Right rim"), (.36, LEFT, "--", "Left mirror")]:
        fig.add_artist(Line2D([pos, pos+.045], [.736, .736], transform=fig.transFigure,
                              color=color, lw=2.7, ls=style))
        fig.text(pos+.057, .736, label, va="center", color=color, fontsize=13, weight="bold")
    fig.text(.93, .736, f"Finite norm cutoff  {cutoff:,}", ha="right", va="center",
             color=INK, fontsize=13)
    ax = fig.add_axes([.115, .225, .815, .445])
    style_axes(ax)
    ax.set(xlim=(0, 2*math.pi), ylim=(-.10, math.pi+.10))
    ax.set_xticks([0, math.pi/2, math.pi, 3*math.pi/2, 2*math.pi], ["0", "π/2", "π", "3π/2", "2π"])
    ax.set_yticks([0, .91, math.pi/2, math.pi], ["0", "0.91", "π/2", "π"])
    ax.grid(axis="y", color=GRID, linewidth=.65)
    ax.axhline(.91, color="#719394", lw=1.1, ls=":")
    ax.axhline(0, color=INK, lw=1)
    ax.plot(x, distances[0], lw=2.6, color=RIGHT, solid_capstyle="round")
    # Add the resolved crossings to the drawing so each cusp touches the zero-distance axis.
    left_curve = sorted(list(zip(x, distances[1])) + [(root, 0) for root in roots])
    xx, yy = zip(*left_curve)
    ax.plot(xx, yy, lw=2.2, ls="--", color=LEFT, dash_capstyle="round")
    ax.scatter(roots, [0, 0], marker="D", color=LEFT, ec=PAPER, lw=.85, s=49, zorder=4)
    ax.set_xlabel("Position on the right circle (radians)", fontsize=13, color=INK)
    ax.set_ylabel("Phase distance\n(radians)", fontsize=12, color=INK)
    fig.text(.064, .077, "The right curve stays above 0.91. The two diamonds mark left inputs reaching 3.9.",
             color=INK, fontsize=12)
    fig.text(.064, .030, "25 measured cutoffs shown; all 193 passed the circle test. The full Gaussian zero count remains open.",
             color=MUTED, fontsize=10.5)
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
