"""Build math-only publication figures from the archived measurements and renderers.

Use --figure to rebuild one figure. The spire requires the original CUDA Lab
dependencies. With --spire-cache PATH it can reuse verified RGB data between runs.
"""

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import Rectangle
import mpmath as mp
import numpy as np
from PIL import Image

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "archive"
FIGURES = ROOT / "docs" / "figures"
ORIGINALS = ARCHIVE / "2026-11-18-research-figures-v001"
INK, GRID = "#183642", "#d7dfdf"
TEAL, RUST, PAPER = "#087973", "#a7472a", "#fbfaf6"
sys.dont_write_bytecode = True


def save(figure, name):
    FIGURES.mkdir(parents=True, exist_ok=True)
    figure.savefig(FIGURES / f"proof-{name}.png", dpi=175, facecolor=PAPER)
    plt.close(figure)


def quartic():
    source = runpy.run_path(str(ARCHIVE / "2026-11-18-quartic-ovals-v001/plot_quartic_ovals.py"))
    ordinate, radial = source["ordinate"], source["radial_coordinates"]
    blue, gold, magenta = source["UPPER"], source["LOWER"], source["MARK"]
    fig, (aff, comp) = plt.subplots(1, 2, figsize=(11, 3.7), layout="constrained")
    x = np.linspace(-4.7, 5.1, 1800)
    theta = np.linspace(-np.pi, np.pi, 2401)
    norm, norm_e = np.hypot(x, 1), np.hypot(np.e, 1)
    y, y_e = ordinate(x/norm, 1/norm), ordinate(np.e/norm_e, 1/norm_e)
    comp.plot(2*np.cos(theta), 2*np.sin(theta), "--", color=GRID, lw=1)
    comp.plot((-3.16, 0), (0, 0), ":", color=GRID)
    for sign, color in ((1, blue), (-1, gold)):
        aff.axhline(sign, color=GRID, linestyle="--", lw=1)
        aff.plot(x, sign*y, color=color, lw=2.6)
        comp.plot(*radial(theta, sign), color=color, lw=2.6)
        comp.scatter([-2-sign], [0], s=36, c=PAPER, edgecolor=color, zorder=3)
    aff.axvline(np.e, ls=":", color=magenta, lw=1)
    aff.scatter(np.e, y_e, color=magenta, zorder=3)
    xe, ye = radial(2*np.arctan(np.e), 1)
    comp.scatter(xe, ye, color=magenta, zorder=3)
    comp.annotate(r"$x=e$", (xe, ye), (-2.8, 2.6), color=magenta,
                  arrowprops=dict(arrowstyle="-", color=magenta))
    comp.annotate(r"$x=\infty$", (-3, 0), (-3.8, -.85),
                  arrowprops=dict(arrowstyle="-", color=INK))
    aff.set(xlim=(-4.7, 5.1), ylim=(-1.57, 1.57), xlabel=r"$x$", ylabel=r"$\widetilde Y$",
            xticks=[-4, -2, 0, 2, 4], yticks=[-1, 0, 1])
    comp.set(xlim=(-3.9, 3.5), ylim=(-3, 3), aspect="equal")
    comp.set_axis_off()
    save(fig, "quartic-ovals")


def pi_hat():
    T = runpy.run_path(str(ORIGINALS / "plot_pi_hat.py"))["target"]
    with mp.workdps(85):
        n = 465*mp.e**2 - 183*mp.e - 659
        d = 155*mp.e**2 + 396*mp.e - 936
        y = (3*d-n+mp.sqrt((n-d)**2+4*n**2))/(2*(n-d))
        scale = mp.mpf("1e20")
        dx = float(scale*(y-mp.pi))
        gap = float(scale*(n/d-T(mp.pi)))
        x = [mp.mpf(k)/20 for k in range(-296, 127)]
        curve = [float(scale*(T(mp.pi+t/scale)-T(mp.pi))) for t in x]
    assert abs(dx + 8.682007272725) < 1e-11
    fig, ax = plt.subplots(figsize=(8.8, 3.8), layout="constrained")
    ax.plot(list(map(float, x)), curve, color="#235e99", lw=2.5)
    ax.axhline(gap, color=RUST, ls="--", lw=1.7)
    ax.axhline(0, color=GRID, lw=1)
    ax.vlines(dx, 0, gap, color=RUST, ls=":", lw=1.3)
    ax.scatter([dx, 0], [gap, 0], color=[RUST, "#235e99"], zorder=3)
    for label, xy in [(r"$\widehat{\pi}$", (dx, gap)), (r"$\pi$", (0, 0))]:
        ax.annotate(label, xy, xytext=(6, 7), textcoords="offset points")
    ax.set(xlabel=r"$10^{20}(y-\pi)$", ylabel=r"$10^{20}(T(y)-T(\pi))$",
           xlim=(-15, 6.3), ylim=(-2, 4.85))
    ax.grid(color=GRID, linewidth=.6)
    save(fig, "pi-hat")


def spire(cache):
    source = runpy.run_path(str(ORIGINALS / "render_dottie_spire.py"))
    record = json.loads((ORIGINALS / "dottie-spire-render.json").read_text())
    if cache and cache.is_file():
        with np.load(cache, allow_pickle=False) as stored:
            grids = [stored[str(i)] for i in range(2)]
    else:
        sys.path.insert(0, str(ORIGINALS / "lab_source"))
        import engine
        import gpu_engine
        import mapping
        grids = [source["render_panel"](view, engine, gpu_engine, mapping, np)[0] for view in source["VIEWS"]]
    for grid, panel in zip(grids, record["panels"], strict=True):
        assert hashlib.sha256(grid.tobytes()).hexdigest() == panel["color_raster_sha256"]
    if cache and not cache.is_file():
        np.savez_compressed(cache, **{str(i): a for i, a in enumerate(grids)})
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.8), width_ratios=[1.42, 1], layout="constrained")
    for ax, panel, grid in zip(axes, record["panels"], grids, strict=True):
        low, high = map(float, panel["real"])
        bottom, top = map(float, panel["imag"])
        ax.imshow(grid, extent=(low, high, bottom, top), origin="upper", interpolation="nearest", aspect="auto")
        ax.scatter(0, float(record["dottie_tip_im"]), s=40, c="white", edgecolor=INK)
        ax.set(xlabel=r"$\Re L$", ylabel=r"$\Im L$")
    axes[0].add_patch(Rectangle((low, bottom), high-low, top-bottom, fill=False,
                                lw=1.1, ls="--", ec="white"))
    save(fig, "dottie-spire")


def reversal():
    source = ARCHIVE / "2026-11-18-lean-foundations-v001/papers/foundations/figures/reversal_order_effect.png"
    raster = np.array(Image.open(source).convert("RGB"))
    assert raster.shape == (795, 2070, 3)
    # The preprint retained the figure, not the raw classifier arrays. Take the
    # three plot interiors from its original pixels, excluding their text and frames.
    fig, axes = plt.subplots(1, 3, sharey=True, figsize=(12, 3.55), layout="constrained")
    for ax, (left, right) in zip(axes, [(153, 701), (812, 1360), (1471, 2020)], strict=True):
        ax.imshow(raster[97:659, left:right], extent=(-4, 4, -np.pi, np.pi), origin="upper",
                  interpolation="nearest", aspect="auto")
        ax.set(xticks=[-4, -2, 0, 2, 4], yticks=[-np.pi, 0, np.pi],
               yticklabels=[r"$-\pi$", "0", r"$\pi$"], xlabel=r"$\Re L$")
    axes[0].set_ylabel(r"$\Im L$")
    save(fig, "reversal")


def two_inputs():
    sys.path.insert(0, str(ARCHIVE / "2026-11-20-hurwitz-speed-mean-square-v001"))
    from verify_two_inputs import ROOT_COUNT, PRECISION, ctx, determinant_roots
    ctx.prec = PRECISION
    _, roots = determinant_roots(ROOT_COUNT)
    radii = np.array([float(abs(v)) for v in roots])
    angles = np.array([float(v.arg()) for v in roots])
    m, edge = 301, np.pi/3
    joint = np.linspace(-2*edge, 2*edge, 2*m-1)
    waves = np.exp(-1j*np.outer(joint, np.log(radii))) * (2/radii**2)
    growth = 2*np.sinh(np.outer(joint, angles)/2)**2
    field = growth @ waves.T
    i, j = np.ogrid[:m, :m]
    pixels = np.abs(field[i+j, j-i+m-1])
    assert abs(pixels.max()-.13679094) < 1e-7
    fig, ax = plt.subplots(figsize=(6.8, 5.3), layout="constrained")
    cmap = LinearSegmentedColormap.from_list("angle", ["#f7f6ef", "#e5d6a4", "#dba35d",
                                                      "#b56851", "#713e57", "#362a48"])
    surface = ax.imshow(pixels, origin="lower", extent=(-edge, edge, -edge, edge),
                        cmap=cmap, vmin=0, vmax=.14, interpolation="bilinear", aspect="equal")
    ax.plot([-edge, edge], [edge, -edge], ":", color="#55505a")
    for h in (-edge/2, edge/2):
        for k in (-edge/2, edge/2):
            ax.scatter(h, k, c="white", edgecolor=INK, s=40)
    ticks = [-edge, -edge/2, 0, edge/2, edge]
    tick_labels = [r"$-\pi/3$", r"$-\pi/6$", "0", r"$\pi/6$", r"$\pi/3$"]
    ax.set(xticks=ticks, yticks=ticks, xticklabels=tick_labels, yticklabels=tick_labels,
           xlabel=r"$h$", ylabel=r"$k$")
    bar = fig.colorbar(surface, ax=ax, shrink=.75, ticks=[0, .04, .08, .12, .14])
    bar.set_label(r"$|\Delta K_1|$")
    save(fig, "two-input")


def barnes():
    record = json.loads((ARCHIVE / "2026-11-16-super-zeta-v001/computations/binomial-normalization-results.json").read_text())
    def midpoint(value):
        return float(value.lstrip("[").split()[0])
    levels = [row["N"] for row in record["finite_cutoff_checks"]]
    values = [midpoint(row["direct_normalized_product"]) for row in record["finite_cutoff_checks"]]
    fig, ax = plt.subplots(figsize=(8.8, 3.65), layout="constrained")
    ax.plot(levels, values, "o-", color=TEAL, lw=2)
    ax.axhline(midpoint(record["exact_limit_constant"]), color=RUST, ls="--", lw=1.5)
    ax.set_xscale("log", base=2)
    ax.set(xticks=levels, xticklabels=list(map(str, levels)), xlabel=r"$N$",
           ylabel=r"$N^{1/4}\prod_{n=1}^N C_n$", ylim=(1.11, 1.232))
    ax.grid(axis="y", color=GRID, lw=.7)
    save(fig, "barnes")


if __name__ == "__main__":
    graphs = {"quartic": quartic, "pi": pi_hat, "reversal": reversal, "two-input": two_inputs,
              "barnes": barnes, "spire": spire}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", choices=list(graphs))
    parser.add_argument("--spire-cache", type=Path)
    args = parser.parse_args()
    plt.rcParams.update({"axes.spines.right": False, "axes.spines.top": False,
                         "axes.facecolor": PAPER, "font.size": 12, "axes.labelcolor": INK})
    for name in [args.figure] if args.figure else graphs:
        if name == "spire":
            spire(args.spire_cache)
        else:
            graphs[name]()
