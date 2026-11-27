"""Outward ball replay of the discriminant-23 folded theta integral.

Only the finite logarithmic model is integrated. Its model error is added
separately. Point samples and continuous boxes are reported separately.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction
from math import factorial, isqrt
from time import perf_counter

from flint import __version__, acb, acb_poly, arb, ctx, fmpq


def real(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def interval(lower, upper):
    return real(lower).union(real(upper))


def theta_coefficients(cutoff):
    bound = isqrt(10 * cutoff // 9)
    coef = [0] * (cutoff + 1)
    mass = 0
    for a in range(-bound, bound + 1):
        for b in range(-bound, bound + 1):
            if a == b == 0:
                continue
            principal = a * a + a * b + 6 * b * b
            other = 2 * a * a + a * b + 3 * b * b
            if principal <= cutoff:
                coef[principal] += 1
                mass += 1
            if other <= cutoff:
                coef[other] -= 1
                mass += 1
    return coef, mass


class FoldedModel:
    def __init__(self, cutoff, end, order, digits):
        if order <= 0 or end <= 0 or 18 * order + 9 > 13 * (cutoff + 1):
            raise ValueError("parameters violate the finite theta model hypotheses")
        coefficients, self.mass = theta_coefficients(cutoff)
        self.polynomial = acb_poly(coefficients)
        self.end = end
        self.scale = 2 * arb.pi() / arb(23).sqrt()
        self.model_error = (
            15 * (arb(3) / 11) ** (order - 1)
            + (arb(126) / 5) * (-(arb(5) / 4) * arb(end).exp()).exp()
        )
        self.abs_tol = arb(10) ** -(digits + 4)

    def heat_polynomial(self, u):
        q = (-self.scale * u.exp()).exp()
        return self.polynomial(q)

    def integrate(self, f):
        # All provided integrands are entire in u.
        result = acb.integral(
            lambda u, analytic: f(u), 0, self.end,
            abs_tol=self.abs_tol, rel_tol=self.abs_tol,
        )
        if not result.is_finite():
            raise ArithmeticError("finite-model ball integration did not finish")
        return result

    def central_value(self, height):
        t = real(height)
        return self.integrate(
            lambda u: 2 * (u / 2).exp() * self.heat_polynomial(u) * (t * u).cos()
        ).real

    @lru_cache(maxsize=256)
    def center_coefficients(self, height, degree):
        """Coefficients of the finite model at 1/2 + i*height, through degree."""
        t = real(height)
        coefficients = []
        for k in range(degree + 1):
            oscillation = acb.sin if k % 2 else acb.cos
            coefficient = self.integrate(
                lambda u: 2 * (u / 2).exp() * self.heat_polynomial(u)
                * oscillation(t * u) * u**k / factorial(k)
            ).real
            coefficients.append(acb(0, coefficient) if k % 2 else acb(coefficient))
        return tuple(coefficients)

    def enclosure(self, low_re, high_re, low_im, high_im, degree, derivative):
        height = (low_im + high_im) / 2
        radius = (high_im - low_im) / 2 + max(
            abs(low_re - Fraction(1, 2)), abs(high_re - Fraction(1, 2))
        )
        if 2 * self.end * radius > degree + 1:
            raise ValueError("Taylor ratio exceeds one half")
        z = acb(
            interval(low_re - Fraction(1, 2), high_re - Fraction(1, 2)),
            interval(low_im - height, high_im - height),
        )
        coeffs = self.center_coefficients(height, degree)
        if derivative:
            coeffs = tuple(k * coeffs[k] for k in range(1, degree + 1))
        else:
            coeffs = coeffs[:degree]
        model = acb(0)
        for coefficient in reversed(coeffs):
            model = model * z + coefficient
        # The two amplitudes have norm at most mass each. Differentiating
        # inserts a factor of u <= end and changes the reflected sign.
        remainder = real(
            4 * self.mass * self.end * (self.end if derivative else 1)
            * (self.end * radius) ** degree / factorial(degree)
        )
        return model, self.model_error + remainder


def sample(model, height):
    start = perf_counter()
    finite = model.central_value(height)
    elapsed = perf_counter() - start
    full_reading = finite + model.model_error.upper() * arb(0, 1)
    print(f"t={height} finite={finite.str(16)} model_error={model.model_error.str(6)} "
          f"completed={full_reading.str(12)} "
          f"elapsed_s={elapsed:.4f}", flush=True)


def value_sign(model, height):
    value = model.central_value(height)
    if value > model.model_error:
        return 1
    if -value > model.model_error:
        return -1
    raise ArithmeticError(f"could not determine the central value sign at {height}")


def cover_box(model, box, degree, direction=None):
    """Cover a closed box by nonzero readings or by one signed derivative."""
    todo = [(*box, 0)]
    checked = 0
    smallest = None
    while todo:
        a, b, lo, hi, depth = todo.pop()
        value, error = model.enclosure(a, b, lo, hi, degree, direction is not None)
        projections = (direction * value.imag,) if direction is not None else (
            value.real, -value.real, value.imag, -value.imag,
        )
        for projection in projections:
            if projection > error:
                bound = (projection - error).lower()
                smallest = bound if smallest is None or bound < smallest else smallest
                checked += 1
                break
        else:
            if depth >= 18:
                kind = "slope" if direction is not None else "value"
                raise ArithmeticError(f"unresolved {kind} box {(a, b, lo, hi)}")
            if b - a >= hi - lo:
                mid = (a + b) / 2
                todo.extend(((a, mid, lo, hi, depth + 1), (mid, b, lo, hi, depth + 1)))
            else:
                mid = (lo + hi) / 2
                todo.extend(((a, b, lo, mid, depth + 1), (a, b, mid, hi, depth + 1)))
    return checked, smallest


def check_band(model, lower, upper, step, degree):
    if not 0 <= lower < upper or step <= 0 or degree < 1:
        raise ValueError("expected an increasing nonnegative band and positive step and degree")
    start = perf_counter()
    left, right = Fraction(3, 8), Fraction(5, 8)
    count = 0
    cells = 0
    lo = lower
    sign_lo = value_sign(model, lo)
    smallest = None
    while lo < upper:
        hi = min(lo + step, upper)
        sign_hi = value_sign(model, hi)
        if sign_lo == sign_hi:
            checks = [cover_box(model, (Fraction(0), Fraction(1), lo, hi), degree)]
        else:
            checks = [
                cover_box(model, (left, right, lo, hi), degree, direction=sign_lo),
                cover_box(model, (Fraction(0), left, lo, hi), degree),
                cover_box(model, (right, Fraction(1), lo, hi), degree),
            ]
            count += 1
            print(f"crossing={count} open_height_bracket=({lo},{hi}) direction={sign_lo} "
                  f"slope_lower={checks[0][1].str(8)}", flush=True)
        for checked, margin in checks:
            cells += checked
            smallest = margin if smallest is None or margin < smallest else smallest
        lo, sign_lo = hi, sign_hi
    print(f"band=[{lower},{upper}] full_real_interval=[0,1] positive_simple_zeros={count} "
          f"boxes={cells} minimum_checked_margin={smallest.str(8)} "
          f"elapsed_s={perf_counter() - start:.3f}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=32)
    parser.add_argument("--cutoff", type=int, default=64)
    parser.add_argument("--end", type=int, default=4)
    parser.add_argument("--order", type=int, default=46)
    parser.add_argument("--band", type=Fraction, nargs=2, metavar=("LOWER", "UPPER"))
    parser.add_argument("--step", type=Fraction, default=Fraction(1, 8))
    parser.add_argument("--degree", type=int, default=36)
    parser.add_argument("heights", type=Fraction, nargs="*")
    args = parser.parse_args()
    if not args.heights and not args.band:
        parser.error("supply point heights, a band, or both")
    ctx.dps = args.digits + 12
    model = FoldedModel(args.cutoff, args.end, args.order, args.digits)
    print(f"python_flint={__version__} norm_cutoff={args.cutoff} retained_terms={model.mass} "
          f"u_cutoff={args.end} theta_order={args.order} precision_digits={ctx.dps}", flush=True)
    for height in args.heights:
        sample(model, height)
    if args.band:
        check_band(model, *args.band, args.step, args.degree)


if __name__ == "__main__":
    main()
