"""Replay cap capture and winding on the flanks of the archived Dottie window."""

import argparse
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive_computations", type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.archive_computations.resolve()))

    import verify_dottie_horn_slice as orbit
    from dottie_multiplier_winding import return_scale
    from flint import acb, arb, ctx

    ctx.prec = 384
    x0, y = arb(orbit.OFFSET), arb(orbit.HEIGHT)
    slack = arb("1.4e-21")
    x_band = x0 + arb(0, slack.upper())

    def height(x):
        return 4 * arb.pi() / (orbit.PERIOD * ((x / y) ** 2).log1p())

    center = height(x0)
    lower_offset = height(x0 + slack) - center
    upper_offset = height(x0 - slack) - center
    assert lower_offset < -arb(1) / 4
    assert upper_offset > arb(1) / 4
    print("center", center.str(41))
    print("endpoint offsets", lower_offset.str(24), upper_offset.str(24))

    orbit.DISK_RADIUS = arb("1e-14").upper()
    for flank in (-1, 1):
        lift = acb(flank * x_band, y)
        for phase, rate in (("P", lift), ("Q", -lift)):
            _, capture, residual, contraction = orbit.trapping_data(rate)
            _, winding, _ = return_scale(rate)
            assert contraction < arb("0.232")
            assert winding == -flank
            print(flank, phase, "capture", capture.str(8), "residual", residual.str(8),
                  "derivative", contraction.str(11), "winding", winding)


if __name__ == "__main__":
    main()
