"""Enclose the continued unit-coupling super zeta at two Gaussian zeros and at its vertex.

Run with Python 3 and python-flint 0.9.0. The input is the certified height
interval from the Gaussian detour replay. All claimed inequalities test Arb
balls, including the uncertainty in the entire input interval.
"""

import json
from fractions import Fraction
from math import factorial
from pathlib import Path
import sys

from flint import acb, acb_series, arb, ctx, fmpq

ARCHIVE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ARCHIVE / "2026-11-18-spectral-reproduction-v001"))
from check_complex_mellin import hyperbolic_factors

BRACKET_FILE = ARCHIVE / "2026-11-21-gaussian-pinch-v001" / "central-detours.json"
CUTOFF = 144
PANEL = 3


def exponential_tail(rate, order):
    """Integral of y^order exp(-rate*y) from CUTOFF to infinity."""
    mass = 1 / rate
    for j in range(1, order + 1):
        mass = (CUTOFF**j + j * mass) / rate
    return (-rate * CUTOFF).exp() * mass


def mellin_moment(s, order=0):
    """Integral in y=log(u); order k differentiates exp(-s*y) k times."""
    def integrand(y, analytic):
        _, u, _, sech_squared = hyperbolic_factors(y)
        v = u * sech_squared
        if analytic and not (1 + v).real > 0:
            return acb("nan")
        return (-y)**order * (-s * y).exp() * v.log1p()

    total = acb(0)
    tolerance = arb(2)**-85
    for start in range(-CUTOFF, CUTOFF, PANEL):
        total += acb.integral(
            integrand, start, start + PANEL, abs_tol=tolerance, rel_tol=tolerance,
            eval_limit=3500,
        )
    if not total.is_finite():
        raise ArithmeticError("FLINT did not enclose a finite Mellin panel")
    # log(1+u sech²(sqrt(u))) <= u for u<=1 and <=4 for u>=1.
    # Multiplication by |y|^order covers differentiation under the integral.
    tail = exponential_tail(1 - s.real, order) + 4 * exponential_tail(s.real, order)
    error = arb(0, tail.upper())
    return total + acb(error, error)


def unit_spectrum(s, integral):
    """Equation (24), valid for scalars and truncated complex Taylor series."""
    twice = 2 * s
    pi_power = (-twice * arb.pi().log()).exp()
    two_power = (twice * arb(2).log()).exp()
    reference = 2 * pi_power * (two_power - 1) * twice.zeta()
    return reference + s * s.sin_pi() / arb.pi() * integral


def exact_ball(rational):
    return arb(fmpq(rational.numerator, rational.denominator))


def bracket_image(t_lo, t_hi):
    """The Gaussian inputs are w=1/2+it; the spectral argument is w/2."""
    half_height = (t_lo + t_hi) / 4
    radius = exact_ball((t_hi - t_lo) / 4)
    sigma = arb(1) / 4
    middle = acb(sigma, exact_ball(half_height))
    full = acb(sigma, exact_ball(t_lo / 2).union(exact_ball(t_hi / 2)))
    # Along this vertical interval, |dI/d Im(s)| <= ∫ |y| exp(-sigma*y)L(y)dy.
    # The two half-lines contribute at most 1/(1-sigma)^2 and 4/sigma^2.
    derivative_bound = 1 / (1 - sigma)**2 + 4 / sigma**2
    error = arb(0, (radius * derivative_bound).upper())
    return unit_spectrum(full, mellin_moment(middle) + acb(error, error))


def require_between(value, lower, upper, name):
    if not (arb(lower) < value and value < arb(upper)):
        raise ArithmeticError(f"{name} is outside the required bounds: {value}")


def check_bend():
    # Expand the spectrum in s-1/4 first. On the height trace s=1/4+i*t/2,
    # the linear and quadratic coefficients are i*B and C, respectively.
    sigma = acb(arb(1) / 4)
    s = acb_series([sigma, 1], prec=3)
    integral = acb_series([mellin_moment(sigma, k) / factorial(k) for k in range(3)], prec=3)
    z = unit_spectrum(s, integral)
    # The continuation is real on the real axis; derivatives there are real.
    if not all(z[k].imag.contains(0) for k in range(3)):
        raise ArithmeticError("The real-axis jets exclude the real axis")
    intercept = z[0].real
    b = z[1].real / 2
    c = -z[2].real / 4
    require_between(intercept, "-0.60670972", "-0.60670971", "real intercept")
    require_between(b, "-2.3681900", "-2.3681899", "linear imaginary coefficient")
    require_between(c, "4.8587740", "4.8587741", "quadratic real coefficient")
    require_between(c / b**2, "0.8663505", "0.8663506", "quadratic coefficient in output coordinates")


def main():
    ctx.prec = 160
    data = json.loads(BRACKET_FILE.read_text(encoding="utf-8"))
    t_lo, t_hi = map(Fraction, data["refinement"]["height_bracket"])
    if not 0 < t_lo < t_hi:
        raise ValueError("Expected an ordered positive Gaussian root bracket")
    plus = bracket_image(t_lo, t_hi)
    minus = bracket_image(-t_hi, -t_lo)
    for label, image in (("upper input", plus), ("lower input", minus)):
        require_between(image.real, "-0.35481", "-0.35339", label + " real part")
    require_between(plus.imag, "-0.47364", "-0.47217", "upper input imaginary part")
    require_between(minus.imag, "0.47217", "0.47364", "lower input imaginary part")
    if not minus.imag - plus.imag > arb("0.94434"):
        raise ArithmeticError("The two image enclosures do not establish the separation")
    check_bend()
    print("Both complete height brackets passed; image separation > 0.94434.")
    print("Super-zeta vertex passed: 0.8663505 < C/B^2 < 0.8663506.")


if __name__ == "__main__":
    main()
