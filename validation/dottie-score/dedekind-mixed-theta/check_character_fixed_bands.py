"""Replay the discriminant-23 sign bounds with outward integer arithmetic."""

import argparse
import re
from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

SCALE = 10**24
WEIGHTS = (989, 5888, -928, 10496, -4540, 10496, -928, 5888, 989)
DEGREES = 72
QUADRATURE = Fraction(3, 100_000)
EXPONENTIAL = 264 * Fraction(2 * 18**DEGREES, factorial(DEGREES))
SPARSE_REPLACEMENT = Fraction(1, 20_000_000)


def ceil_ratio(numerator, denominator):
    return -((-numerator) // denominator)


@dataclass(frozen=True)
class Box:
    lo: int
    hi: int

    @staticmethod
    def hull(lower, upper):
        lower, upper = Fraction(lower) * SCALE, Fraction(upper) * SCALE
        return Box(lower.numerator // lower.denominator,
                   ceil_ratio(upper.numerator, upper.denominator))

    @staticmethod
    def point(value):
        return Box.hull(value, value)

    def __add__(self, other):
        return Box(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        corners = (self.lo * other.lo, self.lo * other.hi,
                   self.hi * other.lo, self.hi * other.hi)
        return Box(min(corners) // SCALE, ceil_ratio(max(corners), SCALE))

    def times(self, n):
        if n < 0:
            return (-self).times(-n)
        return Box(n * self.lo, n * self.hi)

    def div(self, n):
        assert n > 0
        return Box(self.lo // n, ceil_ratio(self.hi, n))

    def inflate(self, radius):
        units = Fraction(radius) * SCALE
        n = ceil_ratio(units.numerator, units.denominator)
        return Box(self.lo - n, self.hi + n)

    @property
    def lower(self):
        return Fraction(self.lo, SCALE)

    @property
    def upper(self):
        return Fraction(self.hi, SCALE)


def exp_bound(x):
    reduced = x.div(64)
    assert -SCALE <= reduced.lo <= reduced.hi <= SCALE
    term = total = Box.point(1)
    for k in range(1, 32):
        term = (term * reduced).div(k)
        total += term
    # With |reduced| <= 1, the exponential tail is at most 2/32!.
    total = total.inflate(Fraction(2, factorial(32)))
    for _ in range(6):
        total *= total
    return total


def cos_bound(x):
    reduced = x.div(32)
    assert -SCALE <= reduced.lo <= reduced.hi <= SCALE
    square = -(reduced * reduced)
    term = total = Box.point(1)
    for k in range(1, 16):
        term = (term * square).div((2 * k - 1) * (2 * k))
        total += term
    total = total.inflate(Fraction(1, factorial(32)))
    for _ in range(5):
        total = (total * total).times(2) - Box.point(1)
    return total


def coefficients(source):
    match = re.search(
        r": ℤ :=\s*\[([^\]]+)\]\.getD n 0", source.read_text(encoding="utf-8")
    )
    if match is None:
        raise ValueError(f"No coefficient table in {source}")
    return [int(value.strip()) for value in match[1].split(",")]


def common_nodes(panels):
    numerators = [0] * (panels * 8 + 1)
    for panel in range(panels):
        for node, weight in enumerate(WEIGHTS):
            numerators[8 * panel + node] += weight
    return [(Fraction(3 * node, 8 * panels), Fraction(3 * weight, panels * 28350))
            for node, weight in enumerate(numerators)]


def circle_error(panels):
    ratio = Fraction(6, panels)
    assert ratio < 1
    return 3 * (1 + Fraction(41142, 28350)) * 60 * ratio**10 / (1 - ratio)


def theta_box(polynomial, heat, sparse=False):
    if sparse:
        square = heat * heat
        cube = square * heat
        sixth = cube * cube
        return (heat - square - cube + sixth + sixth * square).times(2)
    total = Box.point(0)
    for a in reversed(polynomial):
        total = total * heat + Box.point(a)
    return total


def samples(polynomial, panels, sparse=False):
    alpha = Box.hull(Fraction(1310134702738, 10**12), Fraction(1310134702739, 10**12))
    for node, weight in common_nodes(panels):
        u = Box.point(node)
        half = exp_bound(u.div(2))
        q = exp_bound(-(alpha * half * half))
        yield node, u, (Box.point(weight) * half * theta_box(polynomial, q, sparse)).times(2)


def moments(polynomial, sparse):
    values = [Box.point(0) for _ in range(DEGREES)]
    derivatives = [Box.point(0) for _ in range(DEGREES)]
    for _, u, term in samples(polynomial, 32, sparse):
        step = u.times(6)
        for k in range(DEGREES):
            if k % 2 == 0:
                values[k] += term
            else:
                derivatives[k] += u * term
            term = (term * step).div(k + 1)
    return values, derivatives


def center_polynomial(data, height):
    center = Box.point(height / 6)
    powers = [Box.point(1)]
    for _ in range(1, len(data)):
        powers.append(powers[-1] * center)
    result = []
    for k in range(len(data)):
        real = imaginary = Box.point(0)
        for j in range(k, len(data)):
            term = (data[j] * powers[j - k]).times(comb(j, k))
            phase = (j - k) % 4
            if phase % 2 == 0:
                real += term if phase == 0 else -term
            else:
                imaginary += term if phase == 1 else -term
        result.append((real, imaginary))
    return result


def lower_decimal(value, digits=12):
    scaled = value * 10**digits
    rounded = scaled.numerator // scaled.denominator
    sign = "-" if rounded < 0 else ""
    whole, fraction = divmod(abs(rounded), 10**digits)
    return f"{sign}{whole}.{fraction:0{digits}d}"


def verify_band(data, low, high, rows, error, derivative=False, sign=1):
    threshold = Fraction(1, 100_000)
    width = (high - low) / rows
    terminal = []
    cells = [(Fraction(0), Fraction(1), low + j * width, low + (j + 1) * width, 0)
             for j in range(rows)]
    cached = {}
    while cells:
        left, right, bottom, top, depth = cells.pop()
        center = (bottom + top) / 2
        if center not in cached:
            cached[center] = center_polynomial(data, center)
        x = Box.hull((left - Fraction(1, 2)) / 6, (right - Fraction(1, 2)) / 6)
        y = Box.hull((bottom - center) / 6, (top - center) / 6)
        real = imaginary = Box.point(0)
        for a, b in reversed(cached[center]):
            real, imaginary = a + x * real - y * imaginary, b + x * imaginary + y * real
        signed = (imaginary if derivative else real).times(sign)
        lower = signed.lower - error
        if lower > threshold:
            terminal.append(lower)
        elif depth >= 16:
            raise ValueError(f"Could not certify {left, right, bottom, top}")
        elif right - left >= 2 * (top - bottom):
            middle = (left + right) / 2
            cells.extend([(left, middle, bottom, top, depth + 1),
                          (middle, right, bottom, top, depth + 1)])
        else:
            cells.extend([(left, right, bottom, center, depth + 1),
                          (left, right, center, top, depth + 1)])
    print(f"[{low}, {high}] cells={len(terminal)} signed_lower>={lower_decimal(min(terminal))}")


def eta_product_prefix(degree):
    data = [0] * (degree + 1)
    data[1] = 2
    for step in (1, 23):
        for power in range(step, degree + 1, step):
            for j in range(degree, power - 1, -1):
                data[j] -= data[j - power]
    return data


def check_density_bound(poly):
    assert poly[0] == 0
    assert sum(abs(a) * Fraction(2, 5)**(k - 1) for k, a in enumerate(poly) if k) <= 5


def verify_reference_bracket():
    # Use the classical all-degree eta identity here. Each factor's
    # pentagonal coefficients have size at most one, so the doubled
    # product coefficient in degree n is bounded by 2n.
    d, panels = 60, 256
    poly = eta_product_prefix(d)
    check_density_bound(poly)
    q = Fraction(3, 11)
    assert sum(Fraction(3)**k / factorial(k) for k in range(10)) > 20
    assert sum(Fraction(1, factorial(k)) for k in range(5)) > Fraction(27, 10)
    # The compact theta tail uses the integration length 3 and
    # the bound 2*exp(3) <= 54 for the folded exponential weight.
    heat_tail = 3 * 54 * 2 * q**(d + 1) * ((d + 1) / (1 - q) + q / (1 - q)**2)
    # On the real axis the doubled eta product is at most 2q;
    # the cutoff tail is bounded by 4*exp(-alpha*exp(3))/alpha.
    cutoff_tail = Fraction(40, 13) * Fraction(10, 27)**26
    error = circle_error(panels) + heat_tail + cutoff_tail
    assert error < Fraction(1, 50_000_000_000)
    pair = ((Fraction(511568332, 10**8), 1), (Fraction(511568334, 10**8), -1))
    totals = [Box.point(0) for _ in pair]
    for node, _, weight in samples(poly, panels):
        for i, (height, _) in enumerate(pair):
            totals[i] += weight * cos_bound(Box.point(height * node))
    for (height, sign), total in zip(pair, totals):
        lower = total.times(sign).lower - error
        assert lower > 0
        print(f"eta reference t={height} signed_lower>={lower_decimal(lower, 15)}")
    print("eta reference total error < 1/50000000000")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("coefficients", type=Path)
    parser.add_argument("--sparse", action="store_true")
    parser.add_argument("--reference-bracket", action="store_true")
    args = parser.parse_args()

    assert circle_error(32) < QUADRATURE
    assert EXPONENTIAL < Fraction(1, 10**10)
    assert sum(abs(weight) for weight in WEIGHTS) == 41142
    assert Fraction(3 * 41142, 28350) < Fraction(22, 5)
    polynomial = coefficients(args.coefficients)
    if args.sparse:
        assert polynomial[:13] == [0, 2, -2, -2, 0, 0, 2, 0, 2, 0, 0, 0, 0]
        polynomial = polynomial[:13]
    check_density_bound(polynomial)
    replacement = SPARSE_REPLACEMENT if args.sparse else 0
    error = QUADRATURE + EXPONENTIAL + replacement
    print(f"scale={SCALE} nodes={len(common_nodes(32))} coefficients={DEGREES} "
          f"quadrature<={QUADRATURE} exponential<{Fraction(1, 10**10)} replacement<={replacement}")
    values, derivatives = moments(polynomial, args.sparse)
    verify_band(values, Fraction(7, 6), Fraction(9, 2), 16, error)
    verify_band(derivatives, Fraction(9, 2), Fraction(83, 16), 14, error, derivative=True)
    verify_band(values, Fraction(83, 16), Fraction(11, 2), 8, error, sign=-1)
    if args.reference_bracket:
        verify_reference_bracket()


if __name__ == "__main__":
    main()

