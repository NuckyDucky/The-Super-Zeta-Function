"""Check the three compact-model signs with outward interval arithmetic.

Use composite Simpson quadrature in the log coordinate and Taylor enclosures
of its finite exponential sum on each height cell.
"""

import re
from fractions import Fraction
from functools import lru_cache
from math import factorial
from pathlib import Path

from mpmath import iv

iv.dps = 45
NODES = 512
DEGREE = 24


def exact(value):
    value = Fraction(value)
    return iv.mpf(value.numerator) / value.denominator


def interval(lower, upper):
    return iv.mpf([exact(lower).a, exact(upper).b])


def polynomial_coefficients():
    source = Path(__file__).resolve().with_name("DedekindDiscriminant23CharacterPolynomial.lean")
    match = re.search(r": ℤ :=\s*\[([^\]]+)\]\.getD n 0", source.read_text(encoding="utf-8"))
    assert match is not None
    coefficients = [int(value.strip()) for value in match.group(1).split(",")]
    assert len(coefficients) == 33 and coefficients[0] == 0
    return coefficients


COEFFICIENTS = polynomial_coefficients()


def polynomial(q):
    value = iv.mpf(0)
    for coefficient in reversed(COEFFICIENTS):
        value = coefficient + value * q
    return value


ALPHA = interval(Fraction(1310134702738, 10**12), Fraction(1310134702739, 10**12))
assert ALPHA.a > exact(Fraction(13, 10))
assert sum(abs(c) * Fraction(2, 5) ** (n - 1) for n, c in enumerate(COEFFICIENTS[1:], 1)) < 5
assert iv.exp(exact(Fraction(15, 16))).a > exact(Fraction(5, 2))
assert iv.exp(exact(Fraction(13, 8))).b < 6
assert iv.exp(exact(Fraction(3, 2))).b < 5
assert iv.exp(3).b < 27

# On a u-circle of radius 1/4, alpha*cos(Im u) >= 5/4
# and |q| <= exp(-15/16) < 2/5. The two exponential weights
# are bounded by 6*exp(Re u) each. Also exp(Re u)*|q| <= 3/10,
# so the value integrand has norm <= 18, and its w derivative
# has norm <= (13/4)*18 < 60. Cauchy's estimate gives
# a fourth real derivative bound of 4!*4^4*60 for both projections.
step = Fraction(3, NODES)
quadrature_error = Fraction(3 * factorial(4) * 4**4 * 60, 180) * step**4

# Each expansion rectangle stays within distance 1 of its center.
# The sum of the absolute Simpson-weighted amplitudes of the two
# exponentials at the center is <= 3*2*5*2 = 60.
# For the derivative, the extra u multiplies that bound by at most 3.
taylor_error = Fraction(180 * 27 * 3 ** (DEGREE + 1), factorial(DEGREE + 1))
error = exact(quadrature_error + taylor_error)
required = exact(Fraction(1, 100000))


def sample_weights():
    result = []
    for index in range(NODES + 1):
        u = exact(step * index)
        endpoint_weight = 1 if index in (0, NODES) else (4 if index % 2 else 2)
        q = iv.exp(-ALPHA * iv.exp(u))
        base = exact(step * endpoint_weight / 3) * polynomial(q) * iv.exp(u / 2)
        row = [2 * base]
        for order in range(1, DEGREE + 2):
            row.append(row[-1] * u / order)
        result.append((u, row))
    return result


SAMPLES = sample_weights()


@lru_cache(maxsize=None)
def centered_coefficients(height):
    coefficients = [iv.mpf(0) for _ in range(DEGREE + 2)]
    for u, weights in SAMPLES:
        phase = exact(height) * u
        cos, sin = iv.cos(phase), iv.sin(phase)
        for k, weight in enumerate(weights):
            coefficients[k] += weight * (sin if k % 2 else cos)
    return tuple(iv.mpc(0, a) if k % 2 else iv.mpc(a, 0) for k, a in enumerate(coefficients))


def enclosure(low_re, high_re, low_im, high_im, derivative):
    height = (low_im + high_im) / 2
    center_re = Fraction(1, 2)
    radius_bound = max(abs(low_re - center_re), abs(high_re - center_re)) + (high_im - low_im) / 2
    assert radius_bound <= 1
    z = iv.mpc(interval(low_re - center_re, high_re - center_re),
               interval(low_im - height, high_im - height))
    coefficients = centered_coefficients(height)
    if derivative:
        coefficients = tuple(k * a for k, a in enumerate(coefficients) if k)
    estimate = iv.mpc(0)
    for coefficient in reversed(coefficients[:DEGREE + 1]):
        estimate = estimate * z + coefficient
    return estimate.imag if derivative else estimate.real


def verify_band(low, high, rows, derivative=False, sign=1):
    width = (high - low) / rows
    cells = [(Fraction(0), Fraction(1), low + j * width, low + (j + 1) * width, 0)
             for j in range(rows)]
    checked = 0
    smallest = None
    while cells:
        x0, x1, y0, y1, depth = cells.pop()
        projected = sign * enclosure(x0, x1, y0, y1, derivative)
        lower = projected.a - error
        if lower > required:
            checked += 1
            if smallest is None or lower.a < smallest.a:
                smallest = lower
            continue
        if depth >= 16:
            raise ValueError(f"could not certify {(x0, x1, y0, y1)}: {projected}")
        if x1 - x0 >= 2 * (y1 - y0):
            x = (x0 + x1) / 2
            cells.extend([(x0, x, y0, y1, depth + 1), (x, x1, y0, y1, depth + 1)])
        else:
            y = (y0 + y1) / 2
            cells.extend([(x0, x1, y0, y, depth + 1), (x0, x1, y, y1, depth + 1)])
    print(f"[{low}, {high}] checked_cells={checked} signed_lower={smallest.a}", flush=True)


def main():
    print(f"quadrature_error={quadrature_error}; taylor_error={taylor_error}", flush=True)
    verify_band(Fraction(7, 6), Fraction(9, 2), 16)
    verify_band(Fraction(9, 2), Fraction(83, 16), 14, derivative=True)
    verify_band(Fraction(83, 16), Fraction(11, 2), 8, sign=-1)


if __name__ == "__main__":
    main()
