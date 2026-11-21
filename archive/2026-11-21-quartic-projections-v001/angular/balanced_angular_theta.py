"""Direct enclosure of the quartic's angular theta at t = 1/sqrt(D).

Requires numpy and python-flint. The summation uses the one-coordinate Jacobi
weight directly. The predicted phase does not enter the summation.
"""

from math import comb

import numpy as np
from flint import arb, ctx, fmpz


D = 26_509_772_707_289
R = 11_825_711_960_877
SIDE = 9000
PRECISION = 80
LIMB = 1 << 45


def enclosure(side, precision, degree=4):
    assert degree > 0 and degree % 4 == 0
    ctx.prec = 224
    denominator = 1 << precision
    c = arb.pi() / arb(D).sqrt()
    weights = [
        int((denominator * (-c * j**2).exp()).floor().unique_fmpz())
        for j in range(side + 1)
    ]
    # Precompute floor(2^precision exp(-c a^2)) a^j in 45-bit pieces.
    # A row dot product of one piece and its signs fits in a signed int64.
    assert side * LIMB < 1 << 63
    max_bits = (denominator * side**degree).bit_length()
    powers = range((max_bits + 44) // 45)
    pieces = np.array([
        [
            [(weights[a] * a**j // LIMB**t) % LIMB for a in range(1, side + 1)]
            for t in powers
        ] for j in range(degree + 1)
    ], dtype=np.int64)
    real, imag = 0, 0
    modulus = fmpz(D)
    for b in range(side + 1):
        offset = R * b % D
        signs = np.fromiter(
            (fmpz(v).jacobi(modulus) for v in range(offset + 1, offset + side + 1)),
            dtype=np.int64, count=side,
        )
        products = pieces @ signs
        moments = [sum(int(row[t]) * LIMB**t for t in powers) for row in products]
        # Expand (a+ib)^degree. Only the precomputed integer moments depend on a.
        terms = [
            (-1)**(j//2) * comb(degree, j) * b**j * moments[degree-j]
            for j in range(degree + 1)
        ]
        real += weights[b] * sum(terms[::2])
        imag += weights[b] * sum(terms[1::2])
    # The first quadrant (positive real axis included) counts every unit orbit
    # once. Two truncated 1-D weights cost at most 2/denominator per point.
    half_degree = degree // 2
    quantization = arb(2**(half_degree+1) * side**(degree+1) * (side + 1)) / denominator
    # The shell max(a,b)=k has 2k representatives, each bounded by
    # 2^(degree/2) k^degree exp(-c k^2). The decreasing integral bounds the tail.
    u = c * side**2
    assert u > arb(degree + 1)/2
    gamma_polynomial = arb(1)
    for j in range(1, half_degree + 1):
        gamma_polynomial = u**j + j*gamma_polynomial
    tail = 2**half_degree * (-u).exp() * gamma_polynomial / c**(half_degree+1)
    error = arb(0, (quantization + tail).upper())
    return (arb(real)/denominator**2 + error,
            arb(imag)/denominator**2 + error, quantization, tail)


def main():
    real, imag, rounding, tail = enclosure(SIDE, PRECISION)
    assert real > 0 or real < 0
    assert imag > 0 or imag < 0
    phase = (imag/real).atan()
    assert arb("2052992689034975.46544 +/- 18.9").contains(real)
    assert arb("-872605627006358.005750 +/- 18.9").contains(imag)
    assert arb("-0.4019051933750971563 +/- 1.12e-14").contains(phase)
    print(f"Real part: {real.str(21, more=True)}")
    print(f"Imaginary part: {imag.str(21, more=True)}")
    print(f"Signed angle modulo pi: {phase.str(19, more=True)} rad")
    print(f"Weight rounding error per component: < {rounding.upper()}")
    print(f"Omitted lattice tail per component: < {tail.upper()}")
    # The primitive Gauss sum and degree-four Gaussian transform predict
    # tan(phase) = Im(delta^2)/Re(delta^2). Comparison follows the measurement.
    a, b = -5_045_155, 1_027_708
    assert a*a + b*b == D and (a + R*b) % D == 0
    slope = arb(2*a*b)/(a*a-b*b)
    assert (imag/real).contains(slope)
    assert not (imag/real).overlaps(-slope)
    print("The enclosure distinguishes the chosen and conjugate quartic branches.")


if __name__ == "__main__":
    main()
