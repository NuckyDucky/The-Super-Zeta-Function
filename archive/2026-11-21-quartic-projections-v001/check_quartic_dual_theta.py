"""Arithmetic checks for the signed Gaussian lattice and its Fourier transform."""

from math import ceil, exp, gcd, log1p, pi, prod, sqrt


REAL, IMAG = -5045155, 1027708
FACTORS = (41, 457, 1414835497)
D = prod(FACTORS)
R = -REAL * pow(IMAG, -1, D) % D


def symbol(value, prime):
    residue = pow(value % prime, (prime - 1) // 2, prime)
    return -1 if residue == prime - 1 else residue


def chi(value):
    return prod(symbol(value, prime) for prime in FACTORS)


def check_local_spectrum(prime, frequency_pairs):
    # A vector of coefficients of 1, zeta, ..., zeta^(p-1) represents zero
    # precisely when all entries are equal, by the prime cyclotomic polynomial.
    r = R % prime
    residues = [symbol(n, prime) for n in range(prime)]
    for h, k in frequency_pairs:
        counts = [0] * prime
        for b in range(prime):
            for a in range(prime):
                counts[(h*a + k*b) % prime] += residues[(a + r*b) % prime]
        # The target is p*chi(h) times the Gauss sum, or zero off that line.
        scale = prime * residues[h] if (k-r*h) % prime == 0 else 0
        difference = [value - scale * coefficient for value, coefficient in zip(counts, residues)]
        assert min(difference) == max(difference)
    print(f"At {prime}, {len(frequency_pairs)} two-dimensional frequencies matched exactly.")


def angular_theta(prime, scale):
    radius = ceil(sqrt(90/(pi*scale)))
    r = R % prime
    table = [symbol(i, prime) for i in range(prime)]
    terms = (table[(a+r*b) % prime] * complex(a,b)**4 * exp(-pi*scale*(a*a+b*b))
             for a in range(-radius, radius+1) for b in range(-radius, radius+1))
    return sum(terms)/4


def main():
    assert D == REAL**2 + IMAG**2 and gcd(REAL, D) == 1
    assert R == 11825711960877 and (R**2 + 1) % D == 0
    assert [R % p for p in FACTORS] == [32, 109, 516876951]
    assert (REAL*R - IMAG) % D == 0 and chi(REAL) == 1
    assert (chi(3 + 8*R), chi(3 - 8*R)) == (-1, 1)
    assert 5 % 16 == 149 % 16
    assert (chi(2+R), chi(2-R)) == (1,1)
    assert (chi(10+7*R), chi(10-7*R)) == (-1,-1)
    for p in (41, 457):
        pairs = ([(h, k) for h in range(p) for k in range(p)] if p == 41
                 else [(h, (R*h + offset) % p) for h in (0,1,3,5,13) for offset in (0,1)])
        check_local_spectrum(p, pairs)
        for d in (0, 1, 16*R):
            measured = sum(symbol(u, p)*symbol(u+d, p) for u in range(p))
            assert measured == (p-1 if d % p == 0 else -1)
    assert gcd(16*R, D) == 1
    assert prod(p-1 for p in FACTORS) == 25806599447040
    print("The norm-73 shift is nonzero at all three conductor primes.")
    for prime, a, b in ((41, 5, -4), (457, 21, 4)):
        assert a*a + b*b == prime and (a+R*b) % prime == 0
        for scaled_t in (0.7, 1.0, 1.3):
            t = scaled_t/sqrt(prime)
            observed = angular_theta(prime, t)
            predicted = symbol(a, prime)*complex(a,b)**4/(prime**4.5*t**5)
            predicted *= angular_theta(prime, 1/(prime*t)).conjugate()
            assert abs(observed-predicted) < 1e-11 * max(1, abs(observed))
    assert -(3+8j)**4 + (3-8j)**4 == 10560j
    print("Six numerical angular theta controls matched. The full-conductor norm-73 shell is +10560i.")
    for u in range(-40, 41):
        for v in range(-40, 41):
            h, k = REAL*u - IMAG*v, IMAG*u + REAL*v
            assert (k - R*h) % D == 0
            assert h*h + k*k == D*(u*u + v*v)
            assert chi(h) == chi(u-R*v)
    print("All 6561 tested full-conductor dual lattice points have the predicted sign and norm.")
    for counts in ((1,0,2,0), (2,0,0,0), (0,0,2,0), (0,0,0,0)):
        roots = (1, 1j, -1, -1j)
        readings = [sum(a*roots[(j*k)%4] for j,a in enumerate(counts)) for k in range(4)]
        recovered = [sum(z*roots[(-j*k)%4] for k,z in enumerate(readings))/4 for j in range(4)]
        assert recovered == list(counts)
    print("Four character readings recover the four class counts, including the mixed norm 9.")
    dottie_height = pi / (80 * log1p((4749479070945369 / 10**23 / (509892982511772 / 10**15))**2))
    balanced_scale = sqrt(D) * dottie_height / pi
    print(f"First active dual frequency length {1/sqrt(D):.15g}.")
    print(f"Archimedean balance scale {balanced_scale:.12g}; stationary dual norm at 2^28 {balanced_scale**2 / 2**28:.12g}.")


if __name__ == "__main__":
    main()
