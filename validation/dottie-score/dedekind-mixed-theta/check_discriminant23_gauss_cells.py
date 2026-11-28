"""Ball-arithmetic check of the proposed height-20 Gauss box cover."""

import argparse
from fractions import Fraction
from functools import lru_cache
from math import comb
import re
from pathlib import Path

from flint import acb, arb, arb_poly, ctx

ROOT = Path(__file__).resolve().parent
from check_discriminant23_centered import check_band, interval, real, theta_coefficients


class GaussModel:
    def __init__(self, recenter):
        table = (ROOT / "Gauss24PanelTable.lean").read_text(encoding="utf-8")
        if "gauss24Denominator : ℤ := 10 ^ 30" not in table:
            raise ValueError("unexpected denominator in the published quadrature table")
        rows = table.split("def gauss24Table", 1)[1].split("]", 1)[0]
        numbers = [(int(x), int(w)) for x, w in re.findall(r"\((-?\d+), (\d+)\)", rows)]
        if len(numbers) != 24:
            raise ValueError("expected 24 Gauss node and weight pairs")
        denominator = 10**30
        polynomial = arb_poly(theta_coefficients(64)[0])
        alpha = 2 * arb.pi() / arb(23).sqrt()
        self.nodes = []
        for j in range(16):
            for offset, weight in numbers:
                u = real((2 * j + 1 + Fraction(offset, denominator)) / 8)
                q = (-alpha * u.exp()).exp()
                a = real(Fraction(weight, 8 * denominator)) * (u / 2).exp() * polynomial(q)
                self.nodes.append((u, a))
        self.model_error = arb(3) / 10**19
        self.recenter = recenter

    def central_value(self, height):
        t = real(height)
        return sum(2 * a * (t * u).cos() for u, a in self.nodes)

    @lru_cache(maxsize=None)
    def coefficients(self, height, depth):
        t = real(height)
        coeff = [arb(0) for _ in range(depth + 1)]
        for u, amplitude in self.nodes:
            phase = t * u
            cosine, sine = phase.cos(), phase.sin()
            term = 2 * amplitude
            for k in range(depth + 1):
                coeff[k] += term * (sine if k % 2 else cosine)
                term = term * u / (k + 1)
        return tuple(acb(0, a) if k % 2 else acb(a) for k, a in enumerate(coeff))

    def enclosure(self, low_re, high_re, low_im, high_im, depth, derivative):
        height = (low_im + high_im) / 2
        center = round(height)
        if low_im < center - Fraction(1, 2) or high_im > center + Fraction(1, 2):
            raise ValueError("rectangle exceeds the half-height error theorem")
        if depth != 36:
            raise ValueError("the published band error uses exactly 36 coefficients")
        coeff = self.coefficients(center, depth)
        used = [(k + 1) * coeff[k + 1] for k in range(depth)] if derivative else coeff[:depth]
        x0 = (low_re + high_re) / 2 if self.recenter else Fraction(1, 2)
        y0 = height if self.recenter else center
        if self.recenter:
            shift = acb(real(x0 - Fraction(1, 2)), real(y0 - center))
            powers = [acb(1)]
            for _ in range(depth - 1):
                powers.append(powers[-1] * shift)
            used = [sum(used[j] * powers[j - k] * comb(j, k) for j in range(k, depth))
                    for k in range(depth)]
        z = acb(interval(low_re - x0, high_re - x0), interval(low_im - y0, high_im - y0))
        value = acb(0)
        for a in reversed(used):
            value = value * z + a
        return value, self.model_error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=48)
    parser.add_argument("--recenter", action="store_true")
    args = parser.parse_args()
    ctx.dps = args.digits
    check_band(GaussModel(args.recenter), Fraction(19, 2), Fraction(20), Fraction(1, 16), 36)


if __name__ == "__main__":
    main()
