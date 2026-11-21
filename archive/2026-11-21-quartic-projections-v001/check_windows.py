"""Enclose the positive-part window integral of the signed dyadic observable."""

import sys
from pathlib import Path

from flint import arb, ctx, fmpz

sys.path.insert(0, str(Path(__file__).resolve().parents[1]
                       / "2026-11-20-gaussian-reflected-disks-v001"))
from gaussian_inputs import prime_ideals


def compare_with_discriminant(primes, bound, multiples):
    # Reduce the original quartic discriminant in the residue fields directly.
    # At the dyadic place delta is 1 mod (1+i)^5, a local square.
    real, imag = -5045155, 1027708
    norm_delta = real * real + imag * imag
    assert (real - 1) % 8 == imag % 8 == 4
    expected = {}
    for p in primes:
        if p == 2:
            norm, signs = 2, (1,)
        elif p % 4 == 1:
            t = int(fmpz(-1).sqrtmod(p))
            norm = p
            signs = tuple(int(fmpz(real + imag * root).jacobi(p)) for root in (t, -t))
        else:
            norm, signs = p * p, (int(fmpz(norm_delta).jacobi(p)),)
        power, j = norm, 1
        while power <= bound:
            expected[power] = (norm, sum(sign**j for sign in signs))
            power, j = power * norm, j + 1
    assert expected == multiples


def finite_readings(bound):
    primes, ideals = prime_ideals(bound)
    multiples = {}
    for norm, sign in ideals:
        power, value = norm, sign
        while power <= bound:
            prev_norm, prev_value = multiples.get(power, (norm, 0))
            assert prev_norm == norm
            multiples[power] = (norm, prev_value + value)
            power *= norm
            value *= sign
    compare_with_discriminant(primes, bound, multiples)
    coefficients = [arb(0) for _ in range(bound + 1)]
    for n, (norm, weight) in multiples.items():
        coefficients[n] = weight * arb(norm).log()
    assert coefficients[73] == 0
    assert coefficients[13] < 0 and coefficients[37] > 0
    mass, harmonic, readings = [arb(0)], [arb(0)], [arb(0)]
    for n, coefficient in enumerate(coefficients[1:], 1):
        mass.append(mass[-1] + coefficient)
        harmonic.append(harmonic[-1] + coefficient / n)
        half = n // 2
        readings.append(mass[n] - 2 * mass[half] - n * (harmonic[n] - harmonic[half]))
    return readings


def positive(v):
    return (v + abs(v)) / 2


def window(readings, y):
    lower, upper = arb(0), arb(0)
    for n in range(y, y*y):
        left, right = readings[n:n + 2]
        # D is affine between integer cutoffs. Jensen and the endpoint chord
        # enclose its positive-part integral. The weight x^(-3/2) decreases.
        lower += positive((left + right) / 2) / (arb(n + 1).sqrt() * (n + 1))
        upper += (positive(left) + positive(right)) / (2 * arb(n).sqrt() * n)
    return lower, upper


if __name__ == "__main__":
    ctx.prec = 192
    starts = (8, 16, 32, 64, 128, 256)
    readings = finite_readings(max(starts)**2)
    for y in starts:
        lo, hi = window(readings, y)
        print(f"{y}..{y*y}   {lo.str(12)}   {hi.str(12)}")
    late = readings[64:65537]
    assert all(v < 0 for v in late)
    peak = max(range(64, 65537), key=lambda n: readings[n].upper())
    assert all(readings[n] < readings[peak] for n in range(64, 65537) if n != peak)
    print(f"On [64,65536] maximum D at {peak}: {readings[peak].str(18)}")
    print("D is strictly negative throughout. The positive-part integral is exactly zero.")
