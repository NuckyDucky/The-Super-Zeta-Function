"""Certify escape of a continued nonreal bilateral Hurwitz zero.

At shift b the caller has already isolated its branch in the closed disk
|w-node| <= radius. A successful match glues that disk to a unique Fourier
zero for every b up to 1/4. The Fourier tube is centered on
1+log_2(c/(1-2c^2)) + 2*pi*i*k/log(2), with radius 8c and c=cos(2*pi*b).
As b increases to 1/4 the center moves left to infinity and the radius
shrinks to zero. The uniform Rouché estimate is archived alongside the
original Fourier series and its derivation.
"""
from fractions import Fraction
from pathlib import Path
import sys

from flint import arb

OLD = Path(__file__).resolve().parent.parent / "Dottie-Off-Axis-Return"
sys.path.insert(0, str(OLD))
from arithmetic_braid import ball
from signature_fourier_escape import input_geometry, uniform_constants


def certify_escape_at(shift: Fraction, node, radius):
    """Return the uniform certificate when the entire input disk is inside."""
    if not Fraction(1, 6) <= shift < Fraction(1, 4):
        return None
    if not radius >= 0:
        raise ValueError("Expected a nonnegative radius")
    c = (2 * ball(shift)).cos_pi()
    if not (0 < c and c <= arb(1) / 20):
        return None

    scaled_height = node.imag * arb(2).log() / (2 * arb.pi())
    integer = (scaled_height + arb(1) / 2).floor().unique_fmpz()
    if integer is None or integer == 0:
        return None
    mode = int(integer)
    center, _ = input_geometry(c, mode)
    distance = abs(node - center) + radius
    if not distance < 8 * c:
        return None

    return {
        "entry_shift": str(shift),
        "fourier_mode": mode,
        "entry_distance_upper": distance.upper().str(28),
        "entry_tube_radius_lower": (8 * c).lower().str(28),
        "uniform_disk_comparison": uniform_constants(),
        "limit_real": "-infinity",
        "limit_imag_formula": f"2*pi*({mode})/log(2)",
        "limit_imag": center.imag.str(28),
    }
