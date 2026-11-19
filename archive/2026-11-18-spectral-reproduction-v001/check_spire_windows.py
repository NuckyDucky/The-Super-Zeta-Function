"""Replay the three centerline windows in the Dottie manuscript, Table 1.

For H_y(z) = exp(iy conjugate(z)), track closed complex disks with the
384-bit directed stage used in the public certificate. Three laps from the
exact cap 1 give a center for a common trapping disk at each parameter window.
The return disk and derivative bounds cover the whole closed y interval.
"""
from fractions import Fraction
from pathlib import Path
from runpy import run_path

from flint import acb, arb, ctx, fmpq

ARCHIVE = Path(__file__).resolve().parent.parent
TRAPPING_SOURCE = ARCHIVE / "2026-11-18-lean-foundations-v001/checks/dottie_slice.py"
trap = run_path(str(TRAPPING_SOURCE))
stage = trap["stage"]
maximal_proper_divisors = trap["maximal_proper_divisors"]

WINDOWS = (
    (639, "0.5098930698771419799831"),
    (640, "0.5098929835386691077069"),
    (641, "0.5098928862668716592052"),
)


def rational(text):
    value = Fraction(text)
    return fmpq(value.numerator, value.denominator)


def certify(period, midpoint):
    y = arb(rational(midpoint), arb(rational("1e-13")).upper())
    rate = acb(0, y)
    center, cap_radius = acb(1), arb(0)
    for _ in range(3 * period):
        center, cap_radius = stage(center.conjugate(), cap_radius, rate)

    disk_radius = arb(rational("1e-11")).upper()
    if not cap_radius < disk_radius:
        raise ArithmeticError("The marked cap enclosure misses the trapping disk")

    image, radius = center, disk_radius
    contraction = arb(1)
    exclusions = set(maximal_proper_divisors(period))
    divisor_gaps = []
    for k in range(1, period + 1):
        image, radius = stage(image.conjugate(), radius, rate)
        # The real-linear derivative norm of one H_y stage is |y| |H_y(z)|.
        contraction = (contraction * abs(rate) * (abs(image) + radius)).upper()
        if k in exclusions:
            gap = (abs(image - center) - radius - disk_radius).lower()
            if not gap > 0:
                raise ArithmeticError(f"Unresolved divisor {k} for period {period}")
            divisor_gaps.append(gap)

    inward_gap = (disk_radius - abs(image - center) - radius).lower()
    if not inward_gap > 0 or not contraction < 1:
        raise ArithmeticError(f"Return disk or contraction failed for {period}")

    scalar_period = period if period % 2 else period // 2
    print(f"paired period {period}, scalar period {scalar_period}, y = {midpoint} +/- 1e-13")
    print(f"  cap radius <= {cap_radius.upper().str(12)}; inward margin >= {inward_gap.str(12)}")
    print(f"  contraction <= {contraction.str(12)}; smallest divisor gap >= {min(divisor_gaps).str(12)}")


if __name__ == "__main__":
    ctx.prec = 384
    for p, text in WINDOWS:
        certify(p, text)
