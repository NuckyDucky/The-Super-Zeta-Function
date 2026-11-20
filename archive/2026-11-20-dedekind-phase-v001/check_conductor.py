"""Exact checks of the quartic conductor and oriented Gaussian ideal character."""
import json
from math import isqrt, prod

from check_gaussian_branch import multiply_gaussian

DELTA = (-5045155, 1027708)
PRIMES = (41, 457, 1414835497)
SIGNED_PRIME_CHECK_LIMIT = 997


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def unit_residue_sign(n, p):
    r = pow(n % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def i_at_conductor(p):
    real, imag = DELTA
    return (-real * pow(imag, -1, p)) % p


MARKS = tuple((p, i_at_conductor(p)) for p in PRIMES)


def marked_value(z):
    m, n = z
    return prod(unit_residue_sign(m + n * r, p) for p, r in MARKS)


def pair_over_split_prime(p):
    for a in range(1, isqrt(p) + 1):
        b = isqrt(p - a * a)
        if a * a + b * b == p:
            return ((a, b), (a, -b))
    raise AssertionError("no representation of split prime")


def local_sign(p, z):
    """Read splitting independently in the residue field of the given ideal."""
    m, n = z
    if p == 2:
        constant = ((1 - DELTA[0]) // 4 - DELTA[1] // 4) % 2
        roots = [x for x in range(2) if (x*x - x + constant) % 2 == 0]
        assert roots == [0, 1]
        return 1
    if n:
        i_image = -m * pow(n, -1, p) % p
        assert (i_image*i_image + 1) % p == 0
        sign = unit_residue_sign(DELTA[0] + DELTA[1] * i_image, p)
        if p <= SIGNED_PRIME_CHECK_LIMIT:
            c = (1 - DELTA[0]) // 4 - (DELTA[1] // 4) * i_image
            roots = sum((x*x - x + c) % p == 0 for x in range(p))
            assert roots == 1 + sign
        return sign
    # At an inert rational prime the residue field is F_p[i], of order p^2.
    base = tuple(a % p for a in DELTA)
    value = (1, 0)
    exponent = (p*p - 1) // 2
    while exponent:
        if exponent % 2:
            value = tuple(a % p for a in multiply_gaussian(base, value))
        base = tuple(a % p for a in multiply_gaussian(base, base))
        exponent //= 2
    assert value in ((1, 0), (p - 1, 0), (0, 0))
    return -1 if value[0] == p - 1 else value[0]


def check_ideal(p, z):
    mark = marked_value(z)
    assert mark == local_sign(p, z)
    m, n = z
    assert marked_value((-n, m)) == mark
    assert marked_value((m, -n)) * mark == prod(
        unit_residue_sign(m*m + n*n, q) for q in PRIMES
    )
    return mark


def main():
    if not __debug__:
        raise RuntimeError("Run the checker with Python assertions enabled.")
    real, imag = DELTA
    assert real % 4 == 1 and imag % 4 == 0
    norm = real**2 + imag**2
    assert prod(PRIMES) == norm and len(set(PRIMES)) == len(PRIMES)
    assert all(prime(p) and p % 8 == 1 for p in PRIMES)
    for p, r in MARKS:
        assert (r*r+1) % p == (real+imag*r) % p == 0
    cases = []
    rational_primes = [p for p in range(2, SIGNED_PRIME_CHECK_LIMIT+1) if prime(p)]
    for p in rational_primes:
        generators = ([(1, 1)] if p == 2 else
                      pair_over_split_prime(p) if p % 4 == 1 else [(p, 0)])
        for z in generators:
            cases.append((p, z, check_ideal(p, z)))
    ramified = []
    for p, r in MARKS:
        rows = []
        for z in pair_over_split_prime(p):
            value = check_ideal(p, z)
            rows.append(dict(generator=z, value=value))
        assert sum(row["value"] == 0 for row in rows) == 1
        ramified.append(dict(p=p, i_image=r, gaussian_primes=rows))
    assert [check_ideal(73, z) for z in ((3, 8), (3, -8))] == [-1, 1]
    print(json.dumps(dict(delta=DELTA, norm=norm, absolute_discriminant=16*norm,
        conductor_primes=ramified, dyadic_value=check_ideal(2, (1, 1)),
        rational_prime_bound=SIGNED_PRIME_CHECK_LIMIT,
        rational_primes_checked=len(rational_primes), gaussian_ideals_checked=len(cases),
        local_signs_at_13_37_73=[(p, z, s) for p, z, s in cases if p in (13, 37, 73)]),
        indent=2))


if __name__ == "__main__":
    main()
