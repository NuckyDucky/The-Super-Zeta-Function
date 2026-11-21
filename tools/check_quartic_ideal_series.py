"""Compare quartic ideal counts with signed Gaussian ideals and test the spectral identity at w=4."""
import argparse
import json
from math import isqrt
from pathlib import Path
import subprocess
import sys

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "archive/2026-11-20-dedekind-phase-v001"))
from check_conductor import marked_value


def gaussian_coefficients(limit):
    unsigned = [0] * (limit + 1)
    signed = unsigned.copy()
    # Every nonzero principal ideal has one generator in this half-open quadrant.
    for a in range(1, isqrt(limit) + 1):
        for b in range(isqrt(limit - a*a) + 1):
            n = a*a + b*b
            unsigned[n] += 1
            signed[n] += marked_value((a, b))
    return unsigned, signed


def convolve(left, right):
    limit = len(left) - 1
    result = [0] * (limit + 1)
    for a, value in enumerate(left[1:], 1):
        if value:
            for b in range(1, limit // a + 1):
                result[a*b] += value * right[b]
    return result


def pari_coefficients(gp, limit):
    # GP's native computation takes the integral polynomial of sqrt(delta) as its only field input.
    program = (
        "K=nfinit(x^4+10090310*x^2+26509772707289);\n"
        "print(K.disc);\n"
        f"print(Vec(dirzetak(K,{limit})));\nquit()\n"
    )
    run = subprocess.run([gp, "-f", "-q"], input=program, text=True, capture_output=True,
                         check=True, timeout=120)
    lines = run.stdout.strip().splitlines()
    if len(lines) != 2 or lines[0] != "424156363316624":
        raise ValueError(f"Unexpected PARI field result: {run.stderr or run.stdout[:180]}")
    coeffs = json.loads(lines[1])
    if len(coeffs) != limit or not all(isinstance(v, int) and v >= 0 for v in coeffs):
        raise ValueError("Incomplete ideal-count vector")
    return [0, *coeffs]


def agree(left, right, label):
    for n, (a, b) in enumerate(zip(left, right, strict=True)):
        if a != b:
            raise ValueError(f"{label} at norm {n}: {a} versus {b}")


def fourth_weight(coefficients):
    return sum((arb(a) / n**4 for n, a in enumerate(coefficients[1:], 1) if a), arb(0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="path to the PARI/GP executable")
    args = parser.parse_args()
    ctx.prec = 160
    limit = 65536
    base, signed = gaussian_coefficients(limit)
    beta = [0] + [(0, 1, 0, -1)[n % 4] for n in range(1, limit + 1)]
    agree(base, convolve([0] + [1] * limit, beta), "ordinary Gaussian ideal count")
    field = pari_coefficients(args.gp, limit)
    agree(field, convolve(base, signed), "quartic ideal count")

    # At w=4 each Dirichlet-series tail of absolute coefficients is bounded by
    # N^-2 times its sum at 2. The degree d ideal coefficients are bounded by
    # those of zeta^d, and zeta(2)<2. The field tail is nonnegative.
    field_bound = arb(16) / limit**2
    field_reading = fourth_weight(field) + (1 + arb(0, 1)) * (field_bound / 2)
    gaussian_reading = fourth_weight(signed) + arb(0, 1) * (arb(4) / limit**2)
    beta_reading = fourth_weight(beta) + arb(0, 1) * (arb(1) / (3*limit**3))

    # Newton's identity for the first two determinant coefficients (-2, 1/3).
    # From log(1 + t/cosh(sqrt(t))^2) = t - 3 t^2/2 + ..., J(2) = 3.
    trace_two = arb(2)**2 - 2*arb(1)/3
    correction_two = arb(3)
    reference_multiplier = 30 / arb.pi()**4
    spectral_reading = (trace_two - correction_two) / reference_multiplier * beta_reading * gaussian_reading
    if not (field_reading.overlaps(spectral_reading) and
            field_reading.rad() < arb("2e-9") and spectral_reading.rad() < arb("2e-9")):
        raise ValueError(f"Quartic field and spectral enclosures: {field_reading} vs {spectral_reading}")
    print(f"Exact coefficients matched at all {limit} norms.")
    print(f"Signed Gaussian / quartic ideal counts at 73 and 5329: "
          f"{signed[73]}/{field[73]}, {signed[5329]}/{field[5329]}.")
    print("Quartic Dedekind zeta at 4, from PARI ideal counts:", field_reading.str(17, more=True))
    print("From the quartet trace, Mellin correction, beta and Gaussian signs:",
          spectral_reading.str(17, more=True))


if __name__ == "__main__":
    main()
