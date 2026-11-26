"""Replay the actual centered Gaussian prime ramp on the archived mesh.

Python 3.12+ with python-flint, NumPy and Numba. Local coefficients use the
archived prime recurrences with the independent Gaussian-generator sign check
from low_gaussian.py. All real-function arithmetic and the reported bounds use
Arb. The analytic bounds are explained in gaussian-prime-center.md.
"""

import argparse
import json
from math import factorial, isqrt
from pathlib import Path

import numpy as np
from flint import acb, arb, ctx, fmpz
from numba import njit

D = 26509772707289
DELTA_RE, DELTA_IM = -5045155, 1027708
CONDUCTOR = ((41, 32), (457, 109), (1414835497, 516876951))
START, STOP, CELL = 1_000_000, 2_000_000, 10_000


@njit
def pow_mod(a, exponent, p):
    a %= p
    z = 1
    while exponent:
        if exponent % 2:
            z = z * a % p
        a = a * a % p
        exponent //= 2
    return z


@njit
def legendre(a, p):
    z = pow_mod(a, (p - 1) // 2, p)
    return -1 if z == p - 1 else z


@njit
def ray_sign(m, n):
    return (legendre(m + 32 * n, 41)
            * legendre(m + 109 * n, 457)
            * legendre(m + 516876951 * n, 1414835497))


@njit
def sqrt_minus_one(p):
    nonresidue = 2
    while legendre(nonresidue, p) != -1:
        nonresidue += 1
    root = pow_mod(nonresidue, (p - 1) // 4, p)
    assert (root * root + 1) % p == 0
    return root


@njit
def gaussian_coefficients(limit, root_limit):
    # A nonzero stored factor is at most sqrt(limit).
    spf = np.zeros(limit + 1, np.int16)
    for p in range(2, root_limit + 1):
        if spf[p] == 0:
            for n in range(p * p, limit + 1, p):
                if spf[n] == 0:
                    spf[n] = p
    values = np.zeros(limit + 1, np.int16)
    determinants = np.zeros(root_limit + 1, np.int8)
    values[1] = 1
    split_count = inert_square_count = 0
    for n in range(2, limit + 1):
        p = int(spf[n])
        if p == 0:
            p = n
            if p == 2:
                assert ray_sign(1, 1) == 1
                trace, determinant = 1, 0
            elif p % 4 == 3:
                trace, determinant = 0, 0
                if p <= root_limit:
                    determinant = -ray_sign(p, 0)
                    assert -determinant == legendre(D, p)
                    inert_square_count += 1
            else:
                root = sqrt_minus_one(p)
                left = legendre(DELTA_RE + DELTA_IM * root, p)
                right = legendre(DELTA_RE - DELTA_IM * root, p)
                trace, determinant = left + right, left * right
                # Independently take the two generator readings.
                prev, cur = p, min(root, p - root)
                while cur * cur > p:
                    prev, cur = cur, prev % cur
                square = p - cur * cur
                other = int(square ** 0.5)
                while (other + 1) ** 2 <= square:
                    other += 1
                while other ** 2 > square:
                    other -= 1
                assert cur * cur + other * other == p
                u, v = ray_sign(cur, other), ray_sign(cur, -other)
                assert u + v == trace and u * v == determinant
                split_count += 1
            values[n] = trace
            if p <= root_limit:
                determinants[p] = determinant
        else:
            k = n // p
            value = int(values[p]) * int(values[k])
            if k % p == 0:
                value -= int(determinants[p]) * int(values[k // p])
            assert -32768 < value < 32768
            values[n] = value
    return values, split_count, inert_square_count


def direct_quarter_prefix(bound):
    result = [0] * (bound + 1)
    for m in range(1, isqrt(bound) + 1):
        for n in range(isqrt(bound - m * m) + 1):
            result[m * m + n * n] += ray_sign(m, n)
    return result


def block_moments(values, order):
    lower = 1
    while lower < len(values):
        upper = min(len(values) - 1, lower + lower // 16)
        row = values[lower:upper + 1]
        nonzero = np.flatnonzero(row)
        positions = nonzero.tolist()
        terms = row[nonzero].tolist()
        moments = [sum(terms)]
        for _ in range(1, order):
            terms = [p * b for p, b in zip(positions, terms)]
            moments.append(sum(terms))
        yield lower, moments
        lower = upper + 1


def finite_folded_mellin(scale, blocks, w):
    # Moment expansions on norm blocks, then exact incomplete-gamma integrals.
    total = acb(0)
    for lower, moments in blocks:
        y = acb(lower) / scale
        decaying = (-y).exp()
        for exponent in (w, 1 - w):
            prefactor = y ** (-exponent)
            gamma = y.gamma_upper(exponent)
            edge = decaying * y ** exponent
            for j, moment in enumerate(moments):
                if moment:
                    total += prefactor * gamma * (moment * (-1)**j) / (factorial(j) * lower**j)
                gamma = (exponent + j) * gamma + edge
                edge *= y
    assert total.is_finite()
    return total


def enclose_mellin_readings(scale, limit, blocks, order):
    # Upper bound for the absolute divisor-weighted exponential tail.
    width = 2**21
    u = arb(limit + width)
    ratio = (-arb(width) / scale).exp()
    divisor_tail = (-arb(limit) / scale).exp() * (
        (2 * width + width * u.log() + 2 * u.sqrt()) / (1 - ratio)
        + (width**2 / u + width / u.sqrt()) * ratio / (1 - ratio)**2
    )
    unit = scale / limit
    weighted_mass = scale * (1 + arb(limit).log())**2
    coefficient_error = (arb(17) / 16) * weighted_mass / 16**order
    log_scale = scale.log()
    value_error = 2 * coefficient_error + 2 * unit * divisor_tail
    h = arb(2)**(-28)
    third_log_moment = (
        weighted_mass * (log_scale**3 + 3 * log_scale**2 + 6 * log_scale + 6)
        + 6 * unit**4 * divisor_tail
    )
    derivative_error = (
        coefficient_error * (log_scale + order + 1)
        + unit**2 * divisor_tail
        + h**2 * third_log_moment / 6
    )
    value = finite_folded_mellin(scale, blocks, acb(1)).real + arb(0, value_error.upper())
    slope = finite_folded_mellin(scale, blocks, acb(1, h)).imag / h + arb(
        0, derivative_error.upper()
    )
    assert value > 0
    return value, slope, value_error, derivative_error


def primes_through(bound):
    is_prime = bytearray(b"\x01") * (bound + 1)
    for p in range(2, isqrt(bound) + 1):
        if is_prime[p]:
            is_prime[p*p::p] = bytes((bound - p*p) // p + 1)
    return (p for p in range(2, bound + 1) if is_prime[p])


def higher_powers_and_mesh(coefficients, prime_limit):
    prime_correction = arb(0)
    signed_slope = arb(0)
    signed_intercept = arb(0)
    negative_mass = arb(0)
    positive_mass = arb(0)
    points = iter(range(START, STOP + 1, CELL))
    next_point = next(points)
    readings = []
    for p in primes_through(prime_limit):
        while next_point is not None and next_point <= p:
            readings.append((
                next_point, signed_slope * next_point - signed_intercept, negative_mass,
                positive_mass
            ))
            negative_mass, positive_mass = arb(0), arb(0)
            next_point = next(points, None)
        logp = arb(p).log()
        if p == 2:
            prime_correction += logp / 2
        elif p % 4 == 3:
            sign = int(fmpz(D).jacobi(p))
            prime_correction += 2 * logp * sign / (p * p - sign)
        else:
            root = int(fmpz(-1).sqrtmod(p))
            left, right = (int(fmpz(DELTA_RE + k * DELTA_IM * root).jacobi(p))
                           for k in (1, -1))
            assert left + right == coefficients[p]
            prime_correction += logp / p * (
                arb(left**2) / (p - left) + arb(right**2) / (p - right)
            )
        if p < STOP and coefficients[p]:
            weight = logp * int(coefficients[p])
            signed_slope += weight / p
            signed_intercept += weight
            if p > START and p % CELL != 0:
                if coefficients[p] < 0:
                    negative_mass -= weight / p
                else:
                    positive_mass += weight / p
    assert next_point is None
    assert len(readings) == (STOP - START) // CELL + 1
    tail = 2 * (1 + arb(prime_limit).log()) / (prime_limit - 1)
    return prime_correction + arb(0, tail.upper()), tail, readings


def evaluate_mesh(center, raw):
    records = []
    for x, ramp, negative_mass, positive_mass in raw:
        records.append((x, ramp + x * center, CELL * negative_mass / 4, CELL * positive_mass / 4))
    cells = list(zip(records, records[1:]))
    def upper_abs_ratio(left, right):
        l, left_reading, _, _ = left
        _, right_reading, allowance_up, allowance_down = right
        upper = max(left_reading.upper(), right_reading.upper()) + allowance_up
        lower = min(left_reading.lower(), right_reading.lower()) - allowance_down
        return max(upper.upper(), (-lower).upper()) / arb(l).sqrt()

    max_upper = max(upper_abs_ratio(l, r).upper() for l, r in cells)
    signed_upper = max((max(l[1].upper(), r[1].upper()) + r[2]).upper() for l, r in cells)
    signed_lower = min((min(l[1].lower(), r[1].lower()) - r[3]).lower() for l, r in cells)
    return records, max_upper, signed_lower, signed_upper


def fixed_point_table(records):
    # Store outward rational endpoints in hundredths for an exact integer audit.
    rows = []
    for x, value, allowance_up, allowance_down in records:
        rows.append((
            x,
            int((100 * value).lower().floor().unique_fmpz()),
            int((100 * value).upper().ceil().unique_fmpz()),
            int((100 * allowance_up).upper().ceil().unique_fmpz()),
            int((100 * allowance_down).upper().ceil().unique_fmpz()),
        ))
    return rows


def check_window_table(table):
    for (l, lo_l, hi_l, _, _), (_, lo_r, hi_r, up, down) in zip(table, table[1:]):
        lo = min(lo_l, lo_r) - down
        hi = max(hi_l, hi_r) + up
        if not (15200 < lo <= hi < 95400 and 10**6 * hi**2 < 933**2 * 10**4 * l):
            raise ArithmeticError(f"The outward-rounded interval at {l} failed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--bits", type=int, default=160)
    ap.add_argument("--cutoff-power", type=int, choices=(24, 25, 26), default=25)
    ap.add_argument("--prime-cutoff", type=int, default=8_000_000)
    args = ap.parse_args()
    ctx.prec = args.bits
    limit = 2**args.cutoff_power
    order = 13
    if not STOP < args.prime_cutoff <= limit or args.bits < 100:
        ap.error("Require STOP < prime cutoff <= norm cutoff and at least 100 bits.")
    scale = arb(D).sqrt() / arb.pi()
    a, split, inert = gaussian_coefficients(limit, isqrt(limit))
    assert direct_quarter_prefix(10_000) == a[:10_001].tolist()
    assert (a[5], a[13], a[73]) == (2, -2, 0)
    print(f"{split} split primes and {inert} inert squares checked at norm cutoff {limit}.",
          flush=True)
    blocks = list(block_moments(a, order))
    value, slope, ve, de = enclose_mellin_readings(scale, limit, blocks, order)
    c_gaussian = slope / value - scale.log() + arb.const_euler()
    correction, correction_tail, raw = higher_powers_and_mesh(a, args.prime_cutoff)
    center = c_gaussian + correction
    records, max_upper, signed_lower, signed_upper = evaluate_mesh(center, raw)
    table = fixed_point_table(records)
    if args.cutoff_power == 25 and args.prime_cutoff == 8_000_000:
        if not (center > arb("-0.857455") and center < arb("-0.857445")
                and signed_lower > 152 and signed_upper < 954
                and max_upper < arb(933) / 1000):
            raise ArithmeticError("The default computation did not resolve the stated bounds.")
        check_window_table(table)
    result = {
        "bits": args.bits,
        "norm_cutoff": limit,
        "prime_cutoff": args.prime_cutoff,
        "split_prime_labels_checked": split,
        "inert_squares_checked": inert,
        "lattice_prefix_checked_through": 10_000,
        "norm_moment_blocks": len(blocks),
        "norm_moment_order": order,
        "mellin_at_1": str(value),
        "mellin_derivative_at_1": str(slope),
        "mellin_value_error": str(ve),
        "mellin_derivative_error": str(de),
        "gaussian_log_derivative_at_1": str(c_gaussian),
        "higher_prime_powers": str(correction),
        "higher_prime_power_tail": str(correction_tail),
        "ramp_center": str(center),
        "mesh": [START, STOP, CELL],
        "whole_interval_lower": str(signed_lower),
        "whole_interval_upper": str(signed_upper),
        "whole_interval_abs_over_sqrt_x_upper": str(max_upper),
        "sample_enclosure_unit": "1/100",
        "sample_columns": ["x", "lower", "upper", "preceding_cell_upper_error",
                           "preceding_cell_lower_error"],
        "samples": table,
    }
    print(json.dumps({k: v for k, v in result.items() if k != "samples"}, indent=2), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
