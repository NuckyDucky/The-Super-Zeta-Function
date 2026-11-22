"""Compare the full spectral function and a measured finite Gaussian completion.

python side-by-side-gaussian.py /path/to/The-Super-Zeta-Function/archive
Requires python-flint 0.9.0, NumPy and Matplotlib. Coordinates in the CSV use
2048*(Re w-1/2) and 2048*(Im w-T0). Change no height to make the mirror.
"""
import argparse
import csv
import gzip
import hashlib
import io
import json
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import colors
from matplotlib.ticker import MaxNLocator
import matplotlib.tri as mtri
import numpy as np
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
STEM = "side-by-side-gaussian"
N = 2**28


def load_module(label, path):
    spec = spec_from_file_location(label, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def midpoint(x):
    return float(x.mid())


def coordinates():
    # Include the true circular boundary as well as a regular interior grid.
    for j in range(-30, 31):
        for k in range(-30, 31):
            if j*j+k*k < 31**2:
                yield "interior", arb(32+j), arb(k)
    for j in range(256):
        angle = 2*arb.pi()*j/256
        yield "circumference", 32+31*angle.cos(), 31*angle.sin()


def compute(archive):
    source = archive / "2026-11-20-gaussian-circle-phases-v001"
    spectral = load_module("spectral_bounds", HERE / "reflected-modulus-contrast.py")
    audited, *_ = spectral.measure()
    assert audited["log10_relative_error_upper_bound"] == "-155258110290"
    gaussian = load_module("gaussian_circle", source / "replay.py")
    # The Gaussian source initializes its gamma normalization at 192 bits.
    ctx.prec = 384
    root = spectral.first_root()
    log_root = root.log()
    arc = gaussian.arc
    moments_path = source / "moments.json.gz"
    with gzip.open(moments_path, "rt") as stream:
        moments = json.load(stream)["cutoffs"][str(N)]
    assert moments["divided_by_factorial"]
    arc.N = N
    arc.mass = arb(moments["mass"])
    arc.coeff_taylor = [acb(arb(x), arb(y)) for x, y in moments["moments"]]
    arc.order = len(arc.coeff_taylor)-1
    tail_record = json.loads((source / "tail-bound.json").read_text())
    assert tail_record["norm_cutoff"] == N
    tail = arb(tail_record["total_modulus_error"])
    center = arc.partial(arb(1)/2, -arb(1)/512)
    assert center.real > 0 and center.imag.contains(0)
    spectral_error = arb("1e-60")
    distort = 2*spectral_error/(1-spectral_error)
    rows = []
    max_plot_ball = {"spectral_ratio": 0., "spectral_phase_rad": 0.,
                     "gaussian_ratio": 0., "gaussian_phase_rad": 0.}
    min_coverage = float("inf")
    for kind, x, y in coordinates():
        pair = []
        for side, u in [("right", x), ("mirror", -x)]:
            offset = acb(u/2048, y/2048)
            # In Z(w/2), the leading term divided by its value at w0 is
            # exp(-(w-w0)*log u1). The analytic remainder bounds both ends.
            dominant = (-offset*log_root).exp()
            error = arb(0, (abs(dominant)*distort).upper())
            z_ratio = dominant+acb(error, error)
            finite = arc.partial(arb(1)/2+offset.real, -arb(1)/512+offset.imag)
            q = finite/center
            values = [abs(z_ratio), z_ratio.arg(), abs(q), q.arg()]
            if not all(v.is_finite() for v in values):
                raise ArithmeticError("Phase interval crosses the principal cut at a sample")
            for name, value in zip(max_plot_ball, values):
                max_plot_ball[name] = max(max_plot_ball[name], abs(float(value.rad().upper())))
            assert abs(finite) > 0
            min_coverage = min(min_coverage, float((tail/abs(finite)).lower()))
            rows.append([side, kind, midpoint(u), midpoint(y), *map(midpoint, values),
                         midpoint(finite.real), midpoint(finite.imag)])
            pair.append(finite)
        assert (pair[0].conjugate()-pair[1]).contains(0)
    assert max(max_plot_ball.values()) < 1e-8
    columns = ["side", "location", "x_2048", "y_2048", "spectral_abs_ratio",
               "spectral_phase_rad", "finite_gaussian_abs_ratio", "finite_gaussian_phase_rad",
               "finite_gaussian_real", "finite_gaussian_imag"]
    dest = HERE / f"{STEM}.csv.gz"
    with dest.open("wb") as handle, gzip.GzipFile(filename="", fileobj=handle, mode="wb", mtime=0) as zipped:
        with io.TextIOWrapper(zipped, encoding="utf-8", newline="") as text:
            writer = csv.writer(text, lineterminator="\n")
            writer.writerow(columns)
            writer.writerows(rows)
    metadata = dict(
        dottie_height=audited["dottie_height"], reference="w0=1/2+i(T_D-1/512)",
        radius="31/2048", centers_real=["31/64", "33/64"],
        norm_cutoff=N, measured_pairs=len(rows)//2, angular_samples_per_rim=256,
        moments_sha256=hashlib.sha256(moments_path.read_bytes()).hexdigest(),
        gaussian_completion_normalization=tail_record["normalization"],
        finite_gaussian_at_reference=center.str(24),
        uniform_full_gaussian_remainder=tail.str(15),
        min_remainder_bound_divided_by_finite_magnitude_at_samples=min_coverage,
        max_radius_of_coordinate_enclosures=max_plot_ball,
        spectral_relative_error_at_each_input_below="10^-155258110290",
        phase="arg(F(w)/F(w0)), in radians",
        rendering="Piecewise-linear interpolation of enclosed point readings within each disk.")
    (HERE / f"{STEM}.json").write_text(json.dumps(metadata, indent=2)+"\n", encoding="utf-8")
    return rows, metadata


def draw(rows):
    from matplotlib.patches import Circle
    def as_array(side):
        return np.asarray([r[2:8] for r in rows if r[0] == side], dtype=float)
    samples = [as_array("mirror"), as_array("right")]
    joint = np.concatenate(samples)
    fig, axes = plt.subplots(2, 2, figsize=(10.4, 6.5), layout="constrained")
    titles = [[r"Original spectrum  $\mathcal{Z}(w/2;1)$", r"Completed Gaussian prefix  $C_N(w),\ N=2^{28}$"],
              ["", ""]]
    for i, (col, var, palette, title) in enumerate([
        (0, 2, "viridis", r"$|F(w)|\,/\,|F(w_0)|$"),
        (1, 4, "viridis", r"$|F(w)|\,/\,|F(w_0)|$"),
        (0, 3, "RdBu_r", r"$\arg[F(w)/F(w_0)]$  (rad)"),
        (1, 5, "RdBu_r", r"$\arg[F(w)/F(w_0)]$  (rad)")]):
        row = i//2
        ax = axes[row, col]
        limits = joint[:, var].min(), joint[:, var].max()
        if row:
            extent = max(abs(limits[0]), abs(limits[1]))
            norm = colors.Normalize(-extent, extent)
        else:
            norm = colors.Normalize(*limits)
        for sample, cx in zip(samples, [-32,32]):
            mesh = mtri.Triangulation(sample[:,0],sample[:,1])
            artist = ax.tripcolor(mesh, sample[:,var], shading="gouraud", cmap=palette, norm=norm)
            ax.add_patch(Circle((cx,0),31,fill=False,ec="#465561",lw=.65))
        ax.axvline(0,ls=":",lw=1,c="#667780")
        ax.plot([0],[0],"o",ms=3.4,mec="#263944",mfc="white",zorder=4)
        ax.set_aspect("equal")
        ax.set_xlim(-65,65)
        ax.set_ylim(-33,33)
        ax.set_xticks([-63,-32,0,32,63])
        ax.set_yticks([-31,0,31])
        ax.tick_params(labelsize=8,length=3)
        ax.spines[["right","top"]].set_visible(False)
        if row:
            ax.set_xlabel(r"$2048\,(\mathrm{Re}\,w-1/2)$",size=10)
        if not col:
            ax.set_ylabel(r"$2048\,(\mathrm{Im}\,w-T_0)$",size=10)
        if titles[row][col]:
            ax.set_title(titles[row][col],fontsize=13,pad=9)
        bar = fig.colorbar(artist, ax=ax, orientation="horizontal", shrink=.80, pad=.09, aspect=34)
        bar.locator = MaxNLocator(nbins=5)
        bar.update_ticks()
        bar.ax.tick_params(labelsize=8,length=2.5)
        bar.set_label(title,fontsize=10)
    fig.savefig(HERE / f"{STEM}.png", dpi=175, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    rows, record = compute(parser.parse_args().archive)
    draw(rows)
    print(json.dumps(record, indent=2))
