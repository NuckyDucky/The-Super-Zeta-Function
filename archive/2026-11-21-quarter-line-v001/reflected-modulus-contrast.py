"""Arb replay for the normalized modulus contrast at reflected Dottie-disk inputs.

Run with python-flint 0.9.0. Add --figure for the boundary figure (Matplotlib).
The roots, normalizations, and error terms are evaluated without subtracting
two numbers of size 10^(more than a trillion).
"""
import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq


def first_root():
    # The first quadrant root of u+cos(u)=0 is unique in this classified strip.
    # Compare u+cos(u) to its affine part on the boundary of this disk.
    center = acb(
        arb("2.4868856989085602306969570343506579794228285528888314789782397816190"),
        arb("1.8093613412957033190162761001940113256000762244053855882446654624838"),
    )
    radius = arb("1e-65")
    residual = abs(center + center.cos())
    curvature = (abs(center.imag) + radius).cosh()
    assert residual + radius**2 * curvature / 2 < radius * abs(1 - center.sin())
    error = arb(0, radius.upper())
    root = center + acb(error, error)
    assert arb.pi() / 2 < root.real and root.real < arb.pi() and root.imag > 0
    return root


def measure():
    ctx.prec = 384
    root = first_root()
    log_norm = abs(root).log()
    radius = arb(31) / 2048
    center_offset = arb(1) / 64
    ratio = fmpq(4749479070945369, 10**23) / fmpq(509892982511772, 10**15)
    dottie = arb.pi() / (80 * arb(ratio**2).log1p())
    center_height = dottie - arb(1) / 512
    height = (center_height + arb(0, radius.upper())) / 2
    offset_max = center_offset + radius
    sigma = (arb(1) / 2 + arb(0, offset_max.upper())) / 2
    assert sigma > fmpq(7, 32) and sigma < fmpq(9, 32) and height > 100
    # Theorem band_absolute_error divided by the exact modulus |u^(-2s)|.
    log_relative = (
        (70 * (height + 2)).log()
        + (arb(11)/10 - 2 * root.arg()) * height
        + 2 * sigma * log_norm
    )
    log10_relative = log_relative / arb(10).log()
    assert log10_relative < -155258110290
    slack = arb(1) / (arb(10)**60)
    assert log_relative < slack.log()
    # The true multiplicative modulus error on the two normalized readings.
    distortion = (1 + slack) / (1 - slack)
    def bounds(offset):
        dominant_ratio = (-2 * offset * log_norm).exp()
        return 1 - dominant_ratio * distortion, 1 - dominant_ratio / distortion

    def record(offset, lower_limit, upper_limit):
        lower, upper = bounds(offset)
        assert lower > arb(lower_limit) and upper < arb(upper_limit)
        return dict(offset=offset.str(25), lower=lower_limit, upper=upper_limit)

    west = center_offset - radius
    east = center_offset + radius
    def stored(offset):
        lower, upper = bounds(offset)
        # Conservatively round the two Arb bounds outward to 14 decimal places.
        scale = 10 ** 14
        lo = lower.lower() * scale
        hi = upper.upper() * scale
        low_int = int(lo.floor().unique_fmpz())
        high_int = int(hi.ceil().unique_fmpz())
        def decimal(value):
            return f"{value // scale}.{value % scale:014d}"
        return record(offset, decimal(low_int), decimal(high_int))

    readings = {name: stored(offset) for name, offset in
                [("west_rim", west), ("center", center_offset), ("east_rim", east)]}
    # Every point in the disk has west <= Re(w)-1/2 <= east. The height cancels
    # exactly in the dominant ratio. Both upper and lower contrast bounds
    # increase with the offset, since log |u| is positive.
    assert log_norm > 0
    data = {
        "observable": "1 - abs(Z(w/2;1)) / abs(Z((1-conj(w))/2;1))",
        "dottie_height": dottie.str(40),
        "disk_center_height": center_height.str(40),
        "right_center_real": "33/64",
        "disk_radius": "31/2048",
        "log10_relative_error_upper_bound": "-155258110290",
        "log10_of_theorem_upper_estimate_across_both_disks": log10_relative.str(25),
        "contrast": readings,
        "whole_closed_right_disk": [readings["west_rim"]["lower"], readings["east_rim"]["upper"]],
        "scope": "Original super zeta denominator calibration; no evaluation of the full Gaussian numerator.",
    }
    return data, bounds, center_offset, radius


def plot(bounds, center, radius, destination):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MultipleLocator, PercentFormatter

    angles = [i * arb.pi() / 128 for i in range(257)]
    values = [bounds(center + radius * theta.cos())[0] for theta in angles]
    fig, ax = plt.subplots(figsize=(7.4, 3.7), layout="constrained")
    ax.plot([float(theta.mid()) for theta in angles], [float(v.mid()) for v in values],
            color="#176d7b", linewidth=2.4)
    for i, name in [(0, "East rim"), (128, "West rim"), (256, "East rim")]:
        x, y = float(angles[i].mid()), float(values[i].mid())
        ax.scatter(x, y, color="#176d7b", clip_on=False)
        ax.annotate(f"{name}   {100*y:.3f}%", (x, y),
                    xytext=((3 if i == 0 else -3 if i == 256 else 0), 16 if i == 128 else 8),
                    textcoords="offset points", bbox=dict(facecolor="white", edgecolor="none", pad=0.1),
                    ha=("left" if i == 0 else "right" if i == 256 else "center"))
    ax.set_xticks([0, float(arb.pi()/2), float(arb.pi()), float(3*arb.pi()/2), float(2*arb.pi())],
                  ["0", "π/2", "π", "3π/2", "2π"])
    ax.set_xlim(0, float(2*arb.pi()))
    ax.set_ylim(-.002, .078)
    ax.yaxis.set_major_locator(MultipleLocator(.02))
    ax.yaxis.set_major_formatter(PercentFormatter(xmax=1, decimals=0))
    ax.set_xlabel("Angle on right circle (radians)")
    ax.set_ylabel(r"$1-|\mathcal{Z}(w/2;1)|\,/\,|\mathcal{Z}((1-\bar w)/2;1)|$")
    ax.tick_params(length=0, pad=7)
    ax.grid(axis="y", alpha=.27)
    ax.spines[["right", "top"]].set_visible(False)
    fig.savefig(destination, dpi=185)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", action="store_true")
    options = parser.parse_args()
    record_data, contrast_bounds, offset, radius = measure()
    prefix = Path(__file__).resolve()
    prefix.with_suffix(".json").write_text(json.dumps(record_data, indent=2) + "\n", encoding="utf8")
    if options.figure:
        plot(contrast_bounds, offset, radius, prefix.with_suffix(".png"))
    print(json.dumps(record_data, indent=2))

