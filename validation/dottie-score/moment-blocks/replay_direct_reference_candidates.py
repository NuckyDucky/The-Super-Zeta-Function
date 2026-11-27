"""Compute integer candidates for the direct Dottie reference score."""

import argparse
from fractions import Fraction
from math import isqrt
from pathlib import Path
from time import perf_counter

LOG_SCALE = 2**96


def atanh_log_ticks(a, b, terms):
    a_square, b_square = a*a, b*b
    numerator = 2 * LOG_SCALE * a
    ticks = 0
    for k in range(terms - 1, -1, -1):
        ticks = ticks * a_square // b_square + numerator // (b * (2*k + 1))
    return ticks


LOG_TWO = atanh_log_ticks(1, 3, 31)


def mantissa_ticks(n):
    exponent = n.bit_length() - 1
    step = 1 << exponent
    return exponent * LOG_TWO + atanh_log_ticks(n - step, n + step, 31)


MANTISSA = (0, *(mantissa_ticks(n) for n in range(1, 64)))


def log_lower_ticks(n):
    exponent = max(0, n.bit_length() - 6)
    mantissa = n >> exponent
    leading = mantissa << exponent
    return (MANTISSA[mantissa] + exponent * LOG_TWO
            + atanh_log_ticks(n - leading, n + leading, 8))


CUTOFF = 276824064
ROW_COUNT = isqrt(CUTOFF)
BASE = 2**96 * 10**32
COS_SCALE = 2**48
DENOMINATOR = 2**256
CHARACTER_FACTORS = ((41, 32), (457, 109), (1414835497, 516876951))


def scaled_decimal(value, scale):
    result = Fraction(value) * scale
    if result.denominator != 1:
        raise ValueError(f"Nonintegral constant {value}")
    return result.numerator


PI_TICKS = scaled_decimal("3.14159265358979323846264338327950", BASE)
PHASE_TICKS = scaled_decimal("3.92292489981824", BASE)
HEIGHT_FACTOR = scaled_decimal("4526119322477.94344019420732885695", 10**32)
COS_DIVISORS = tuple((4 * BASE)**2 * (2 * k + 1) * (2 * k + 2) for k in range(8, -1, -1))


def row_sign(a, b):
    sign = 1
    for prime, residue in CHARACTER_FACTORS:
        value = pow((a + b * residue) % prime, (prime - 1) // 2, prime)
        if value == 0:
            return 0
        if value == prime - 1:
            sign = -sign
        elif value != 1:
            raise ArithmeticError(f"Unexpected character value modulo {prime}")
    return sign


def weight(n):
    raw = PHASE_TICKS - HEIGHT_FACTOR * log_lower_ticks(n)
    angle = (raw + PI_TICKS) % (2 * PI_TICKS) - PI_TICKS
    square = angle**2
    cosine = 0
    for divisor in COS_DIVISORS:
        cosine = COS_SCALE - cosine * square // divisor
    cosine -= 3
    cosine_four = 8 * cosine**4 - 8 * COS_SCALE**2 * cosine**2 + COS_SCALE**4
    return isqrt(2**128 // n) * cosine_four


def paired_block(row, start, count):
    a = row + 1
    a_square = a*a
    total = 0
    for b in range(start + 1, start + count + 1):
        sign = row_sign(a, b) + row_sign(b, a)
        if sign:
            total += sign * weight(a_square + b*b)
    return total


def score_row(row):
    a = row + 1
    a_square = a*a
    end = isqrt(CUTOFF - a_square)
    axis = row_sign(a, 0) * weight(a_square)
    diagonal = row_sign(a, a) * weight(2*a_square) if row < end else 0
    return axis + diagonal + paired_block(row, 0, min(row, end))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=int)
    parser.add_argument("stop", type=int)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= ROW_COUNT:
        parser.error("Expected a nonempty, zero-based row range within the cutoff")
    start_time = perf_counter()
    first = args.start
    total = 0
    if args.output.exists():
        with args.output.open(encoding="ascii") as stream:
            for line in stream:
                row, ticks = map(int, line.split())
                if row != first or row >= args.stop or not line.endswith("\n"):
                    raise ValueError("The saved rows do not form a complete consecutive prefix")
                total += ticks
                first += 1
    with args.output.open("a", encoding="ascii", newline="\n", buffering=1) as stream:
        for row in range(first, args.stop):
            ticks = score_row(row)
            stream.write(f"{row}\t{ticks}\n")
            total += ticks
    print(f"{args.start},{args.stop},{total},{perf_counter()-start_time:.3f}", flush=True)


if __name__ == "__main__":
    main()
