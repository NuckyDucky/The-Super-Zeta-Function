"""Extend the archived central Gaussian certificate to a closed rectangle."""

import argparse
from decimal import Decimal
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent
CENTRAL = ARCHIVE / "2026-11-21-gaussian-pinch-v001" / "central-detours.json"


def outward_decimal(value, places, *, upper):
    """Record a portable decimal bound, rounding away from the enclosure."""
    scaled = value * 10**places
    integer = scaled.upper().ceil() if upper else scaled.lower().floor()
    return format(Decimal(int(integer.unique_fmpz())).scaleb(-places), "f")


def verify(record):
    ctx.prec = 192
    curvature = arb(record["second_derivative"][1])
    slope = arb(record["lower_bound_minus_height_derivative_over_height"])
    assert record["coefficient_cutoff"] == 2**25
    assert record["minimum_running_signed_sum"] == 1
    assert arb(record["theta_tail_relative_to_exp_minus_u_upper"]) < 1
    assert record["x_domain"] == [0, 18] and record["x_cells"] == 1152
    assert record["endpoint_height_bracket"] == [".25", ".27"]
    assert curvature < 3565602 and slope > 519994
    # See the archived proof of u(18)>40 and |Theta(u)| < 3 exp(-u).
    # For x=18+y, exp(y)>=1+y and x^2<=18^2 exp(2y/18).
    tail_rate = arb(55)/100
    tail = 6*18**2*(18*tail_rate-40).exp()/(40-tail_rate-arb(2)/18)
    arg = arb(18)/20
    distortion = arg.sinh()/arg - 1
    assert distortion < arb("0.1406") and tail < arb("1e-10")
    penalty = distortion*3565602 + tail
    floor = arb(519994)-penalty
    assert floor > arb("18762.56")
    bracket = record["refinement"]["height_bracket"]
    assert bracket == [".25835", ".25838"]
    assert arb(record["refinement"]["lower_endpoint_value"][0]) > 0
    assert arb(record["refinement"]["upper_endpoint_value"][1]) < 0
    blind_margin = 18000 * arb("0.01") * arb(bracket[0])
    assert blind_margin > arb("46.5")
    return dict(
        coefficient_cutoff=record["coefficient_cutoff"], half_width="0.05", height_limit="0.27",
        root_height_bracket=bracket, line_slope_lower=519994, curvature_upper=3565602,
        core_distortion_upper=outward_decimal(distortion, 10, upper=True),
        tail_upper=outward_decimal(tail, 17, upper=True),
        slope_floor_lower=outward_decimal(floor, 2, upper=False),
        slope_floor_used_in_lean=18000, blind_horizontal_offset="0.01",
        blind_imaginary_magnitude_lower="46.5",
    )


def plot(destination):
    import matplotlib.pyplot as plt
    from matplotlib.patches import Rectangle

    fig, ax = plt.subplots(figsize=(6.6, 3.6), layout="constrained")
    ax.add_patch(Rectangle((.45, -.27), .1, .54, facecolor="#e6f0ef",
                           edgecolor="#246b6e", linewidth=1.4))
    ax.axvline(.5, color="#697d83", linestyle="--", lw=1)
    ax.axhline(0, color="#a6b6b8", lw=.65)
    for t, direction in [(.258365, 1), (-.258365, -1)]:
        ax.plot(.5, t, "o", color="#143d55", ms=6.2)
        ax.annotate(r"$G=0$", (.5, t), xytext=(9, -6*direction),
                    textcoords="offset points", va="center", color="#143d55")
    for t, left, right in [(.14,"<",">"), (-.14,">","<")]:
        for real, op in [(.475,left), (.525,right)]:
            ax.text(real, t, r"$\mathrm{Im}\,\Lambda"+op+"0$", ha="center", fontsize=12)
    ax.set(xlim=(.446,.554), ylim=(-.30,.30), xlabel=r"$\mathrm{Re}\,w$",
           ylabel=r"$\mathrm{Im}\,w$", xticks=[.45,.475,.50,.525,.55],
           yticks=[-.27,-.15,0,.15,.27])
    ax.spines[['top','right']].set_visible(False)
    fig.savefig(destination,dpi=165)
    plt.close(fig)


def check_spectrum(bracket):
    sys.path.insert(0, str(ARCHIVE / '2026-11-21-gaussian-zero-fiber-v001'))
    from check_images import mellin_moment, unit_spectrum

    ctx.prec = 160
    sigma0 = arb(1)/4
    low, high = (arb(value)/2 for value in bracket)
    middle = acb(sigma0, (low+high)/2)
    middle_integral = mellin_moment(middle)
    derivative_cap = 1/(1-arb(275)/1000)**2 + 4/(arb(225)/1000)**2
    upper_bounds = []
    for k in range(-50, 50):
        sigma = (sigma0+arb(k)/2000).union(sigma0+arb(k+1)/2000)
        s = acb(sigma, low.union(high))
        error = arb(0, (abs(s-middle)*derivative_cap).upper())
        phi = unit_spectrum(s, middle_integral + acb(error, error))
        assert phi.imag < -arb(1)/5
        upper_bounds.append(phi.imag.upper())
    return outward_decimal(max(upper_bounds), 4, upper=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plot", type=Path, metavar="OUTPUT.png",
                        help="draw the verified rectangle with Matplotlib")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without Python -O so enclosure checks are enabled.")
    result = verify(json.loads(CENTRAL.read_text(encoding="utf-8")))
    result["super_zeta_imaginary_part_upper_in_root_band"] = check_spectrum(result["root_height_bracket"])
    saved = json.loads((HERE / "side-sign.json").read_text(encoding="utf-8"))
    if result != saved:
        raise ValueError(f"Side-sign record differs. Recomputed values:\n{json.dumps(result, indent=2)}")
    print(json.dumps(result, indent=2))
    if args.plot:
        plot(args.plot)


if __name__ == "__main__":
    main()
