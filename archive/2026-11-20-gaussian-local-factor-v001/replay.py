"""Enclose the spiral-phase change upon removing the 404 opposite-sign local factors."""

import json
from pathlib import Path
import sys

from flint import acb, arb, ctx, fmpz_poly

ARCHIVE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ARCHIVE / "2026-11-20-gaussian-reflected-disks-v001"))
from gaussian_inputs import CONDUCTOR, height, prime_ideals


def check_dirichlet_factorization():
    """Clear denominators in the fourth-power identity in each good prime class."""
    x = fmpz_poly([0, 1])
    for xi in (-1, 1):
        for nu in (-1, 1):
            selected = int(xi == 1 and nu == -1)
            left = (1 - x) * (1 - xi*x) * (1 - x*x)**(2*selected)
            right = (1 - x)**(4*selected) * (1 - nu*x) * (1 - xi*nu*x)
            if left != right:
                raise ArithmeticError(f"Polynomial identity failed at {xi}, {nu}")


def opposite_primes():
    primes, ideals = prime_ideals(100000)
    signs = {}
    for norm, sign in ideals:
        signs.setdefault(norm, []).append(sign)
    selected = []
    for p in primes:
        if p % 4 != 1:
            continue
        residues = [pow(p, (q - 1) // 2, q) for q, _ in CONDUCTOR]
        norm_sign = 1
        for value in residues:
            norm_sign *= -1 if value > 1 else value
        opposite = sorted(signs[p]) == [-1, 1]
        if opposite != (norm_sign == -1):
            raise ArithmeticError(f"Norm character mismatch at {p}")
        if opposite:
            selected.append(p)
    assert len(selected) >= 404 and 73 in selected[:404]
    return selected[:404]


def phase_enclosures(primes, sigma, kappa):
    t = height() - arb(1) / 512
    s_center = acb(sigma, t)
    scales = [(-2 * arb(p).log()) for p in primes]
    centers = [(s_center * scale).exp() for scale in scales]
    radius = arb(31) / 2048
    bounds = {}
    for j in range(256):
        turns = arb(j).union(arb(j + 1)) / 256
        theta = 2 * arb.pi() * turns
        delta = radius * acb(theta.cos(), theta.sin())
        total = acb(0)
        for p, scale, center in zip(primes, scales, centers):
            divisor = 1 - center * (scale * delta).exp()
            if not divisor.real > 0:
                raise ArithmeticError(f"Ambiguous logarithm at norm {p}")
            change = divisor.log()
            if p == 73:
                single = change.imag - kappa * change.real
            total += change
        for name, value in (("p73", single), ("first404", total.imag - kappa * total.real)):
            bounds[name] = value if name not in bounds else bounds[name].union(value)
    return bounds


def main():
    ctx.prec = 192
    check_dirichlet_factorization()
    lift = ARCHIVE / "2026-11-19-dottie-plane-atlas-v001" / "atlas" / "phase_lift.json"
    re, im = map(arb, json.loads(lift.read_text())["lifted_log_multiplier"])
    kappa = (im + 2 * arb.pi()) / re
    primes = opposite_primes()
    print(f"{len(primes)} opposite split primes from {primes[0]} to {primes[-1]}.")
    # Outward-rounded endpoints in millionths of a radian.
    margins = {"right": {"p73": (7676, 11138), "first404": (-5241, 3232)},
               "left": {"p73": (10015, 14527), "first404": (-1353, 12468)}}
    for label, sigma in (("right", arb(33)/64), ("left", arb(31)/64)):
        for name, result in phase_enclosures(primes, sigma, kappa).items():
            lo, hi = margins[label][name]
            if not (arb(lo)/10**6 < result < arb(hi)/10**6):
                raise ArithmeticError(f"{label} {name} escaped the recorded enclosure")
            print(f"{label} {name} radians: lower {result.lower().str(12)}, upper {result.upper().str(12)}")


if __name__ == "__main__":
    main()
