"""Enclose the finite Gauss sums in the height-29 Lean theorem using Arb."""

import argparse
from math import isqrt
from pathlib import Path
import re

from flint import acb, arb, ctx


HERE = Path(__file__).resolve().parent
INTEGER = r"(-?\d+)"
GAUSS_ROW = re.compile(rf"\({INTEGER},\s*{INTEGER}\)")
FACTOR_ROW = re.compile(rf"\(⟨{INTEGER},\s*{INTEGER}⟩,\s*⟨{INTEGER},\s*{INTEGER}⟩\)")


def lean_table(path, name, row_pattern, length):
    source = path.read_text(encoding="utf-8")
    match = re.search(rf"(?ms)^(?:private )?def {name} : [^\n]+ := #?\[\n(.*?)^\]", source)
    if match is None:
        raise ValueError(f"Missing Lean declaration {name}")
    table = match[1]
    values = [tuple(map(int, row)) for row in row_pattern.findall(table)]
    if len(values) != length or re.sub(r"[\s,]", "", row_pattern.sub("", table)):
        raise ValueError(f"Unexpected data in Lean declaration {name}")
    return values


def theta_coefficients(limit):
    principal = [0] * (limit + 1)
    other = [0] * (limit + 1)
    radius = isqrt(10 * limit // 9)
    for x in range(-radius, radius + 1):
        for y in range(-radius, radius + 1):
            q1 = x * x + x * y + 6 * y * y
            q2 = 2 * x * x + x * y + 3 * y * y
            if 1 <= q1 <= limit:
                principal[q1] += 1
            if 1 <= q2 <= limit:
                other[q2] += 1
    return principal, other


def evaluate_polynomial(coefficients, q):
    value = arb(0)
    for coefficient in reversed(coefficients):
        value = coefficient + q * value
    return value


def check(gauss_file, factor_file, precision):
    ctx.prec = precision
    gauss_rows = lean_table(gauss_file, "gauss24Table", GAUSS_ROW, 24)
    factors = lean_table(factor_file, "height29FactorData", FACTOR_ROW, 128)
    gauss_scale = 10**30
    factor_scale = 2**128
    theta_scale = 2 * arb.pi() / arb(23).sqrt()
    center = acb(arb(3) / 4, 29)
    principal, other = theta_coefficients(80)
    panels = []
    for panel in range(32):
        for node_num, weight_num in gauss_rows:
            node = arb((2 * panel + 1) * gauss_scale + node_num) / (16 * gauss_scale)
            # 1/16 is the half-width. 1/2 normalizes the full folded integral.
            weight = arb(weight_num) / (32 * gauss_scale)
            q = (-theta_scale * node.exp()).exp()
            p = evaluate_polynomial(principal, q)
            o = evaluate_polynomial(other, q)
            panels.append((node, (center * node).exp(), ((1 - center) * node).exp(),
                           weight * (p + 2 * o), weight * (p - o)))

    upper_bounds = [arb(0), arb(0)]
    for j, (a_re, a_im, b_re, b_im) in enumerate(factors):
        offset = acb(0, 2 * arb.pi() * j / 128).exp() / 2
        w = center + offset
        base = acb(0)
        hecke = acb(0)
        for node, phase_a, phase_b, total, character in panels:
            shift = (offset * node).exp()
            folded = phase_a * shift + phase_b / shift
            base += total * folded
            hecke += character * folded
        base -= (arb(3) / 2) / (w * (1 - w))
        expected = [acb(a_re, a_im) / factor_scale, acb(b_re, b_im) / factor_scale]
        for factor, (value, dyadic) in enumerate(zip([base, hecke], expected, strict=True)):
            error = abs(value - dyadic)
            if not error < arb(8) / 10**26:
                raise ArithmeticError(f"Factor {factor}, sample {j} exceeds its Lean budget")
            upper_bounds[factor] = max(upper_bounds[factor], error.upper())

    print(f"precision_bits={precision} checked_readings={2 * len(factors)} "
          f"nodes_per_reading={len(panels)}")
    print(f"base_error_upper={upper_bounds[0].str(12)}")
    print(f"hecke_error_upper={upper_bounds[1].str(12)}")
    print("Both bounds are below 8e-26.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gauss-table", type=Path, default=HERE / "Gauss24PanelTable.lean")
    parser.add_argument("--factor-table", type=Path,
                        default=HERE / "DedekindDiscriminant23Height29FactorEnclosures.lean")
    parser.add_argument("--precision", type=int, default=288)
    args = parser.parse_args()
    check(args.gauss_table, args.factor_table, args.precision)


if __name__ == "__main__":
    main()
