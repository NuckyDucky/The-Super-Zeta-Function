"""Map the angular spread of the archived 193 Gaussian cutoffs inside both disks."""
import gzip
import json
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from flint import acb, arb
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import Circle

ROOT = Path(__file__).resolve().parents[2]
PHASES = ROOT / "archive/2026-11-20-gaussian-circle-phases-v001"
sys.path.insert(0, str(PHASES))
import replay as phase

RINGS, SECTORS = 48, 256


def sample_points():
    # Exact cell-center angles and radii, enclosed at the archived precision.
    angles = [phase.TAU * (2 * j + 1) / (2 * SECTORS) for j in range(SECTORS)]
    directions = [(theta.cos(), theta.sin()) for theta in angles]
    offsets = []
    for k in range(RINGS):
        radius = arb(31) * (2 * k + 1) / (2 * RINGS)
        offsets.extend((radius * x, radius * y) for x, y in directions)
    # Three additional inputs report independent values exactly at mid-height.
    offsets.extend((arb(x), arb(0)) for x in (0, -31, 31))
    return [(arb(33) / 64 + x / 2048, -arb(1) / 512 + y / 2048) for x, y in offsets]


def measure():
    with gzip.open(PHASES / "moments.json.gz", "rt") as stream:
        records = json.load(stream)["cutoffs"]
    cutoffs = list(range(2**26, 2**28 + 1, 2**20))
    if sorted(map(int, records)) != cutoffs:
        raise ValueError("Unexpected cutoffs")
    points = sample_points()
    base = []
    low, high = np.zeros(len(points)), np.zeros(len(points))
    tol = arb("0.0000004")
    for n in cutoffs:
        rec = records[str(n)]
        if not rec["divided_by_factorial"]:
            raise ValueError("Expected factorial-normalized coefficients")
        model = phase.arc
        model.N, model.mass = n, arb(rec["mass"])
        model.coeff_taylor = [acb(arb(x), arb(y)) for x, y in rec["moments"]]
        model.order = len(model.coeff_taylor) - 1
        values = [model.partial(x, y) for x, y in points]
        if not base:
            if not all(abs(z) > 0 for z in values):
                raise ArithmeticError("Reference sum unresolved")
            base = values
            continue
        mids = []
        for val, ref in zip(values, base):
            ratio = val / ref
            angle = ratio.arg()
            if not (abs(ratio) > 0 and angle.rad() < tol):
                raise ArithmeticError(f"Unresolved phase at cutoff {n}")
            mids.append(float(angle.mid()))
        low = np.minimum(low, mids)
        high = np.maximum(high, mids)
    return high - low


def draw(widths):
    colors = LinearSegmentedColormap.from_list("angular_width", [
        "#182843", "#2b6484", "#58a3b4", "#c4e3d6", "#f2d77e", "#e77d42", "#aa2a2a"])
    radii = np.linspace(0, 31, RINGS + 1)
    angles = np.linspace(0, 2 * np.pi, SECTORS + 1)
    r, t = np.meshgrid(radii, angles, indexing="ij")
    x, y = 32 + r * np.cos(t), r * np.sin(t)
    grid = widths[:-3].reshape(RINGS, SECTORS)
    fig, ax = plt.subplots(figsize=(9, 4.8), layout="constrained")
    fig.patch.set_facecolor("#faf8f2")
    ax.set_facecolor("#faf8f2")
    for sign in (-1, 1):
        cells = ax.pcolormesh(sign * x, y, grid, cmap=colors, shading="flat",
                              vmin=0, vmax=np.pi, rasterized=True)
        ax.add_patch(Circle((sign * 32, 0), 31, fill=False, lw=1, color="#29414b"))
        ax.scatter([sign * 32], [0], marker="+", s=35, linewidth=1, color="white")
    ax.axvline(0, linestyle=":", linewidth=1.1, color="#4e5354")
    ax.set_aspect("equal")
    ax.set(xlim=(-65,65), ylim=(-33,33), xticks=[-63,-32,0,32,63], yticks=[-31,0,31],
           xlabel=r"$2048\,(\mathrm{Re}\,w-1/2)$", ylabel=r"$2048\,(\mathrm{Im}\,w-T_0)$")
    ax.spines[["right","top"]].set_visible(False)
    bar = fig.colorbar(cells, ax=ax, location="bottom", shrink=.77, aspect=48, pad=.14)
    bar.set_ticks([0, np.pi/4, np.pi/2, 3*np.pi/4, np.pi],
                  labels=["0",r"$\pi/4$",r"$\pi/2$",r"$3\pi/4$",r"$\pi$"])
    bar.set_label("Angular spread of the 193 readings (rad)")
    fig.savefig(ROOT / "docs/figures/gaussian-sector-interior.png", dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    widths = measure()
    if not np.all((0 <= widths) & (widths < 2.92)):
        raise ArithmeticError("Sample spread outside the proven disk-wide range")
    draw(widths)
    print(f"{RINGS * SECTORS} cell centers on the right, reflected exactly on the left")
    for name, value in zip(("center", "rim facing critical line", "outermost rim"), widths[-3:]):
        print(f"{name}: {value:.8f} radians")
