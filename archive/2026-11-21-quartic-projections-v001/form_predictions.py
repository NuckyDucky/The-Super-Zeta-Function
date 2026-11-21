"""Choose represented primes first, predict the trace, then read both Gaussian signs."""

from math import isqrt, prod

from sympy import isprime, legendre_symbol, sqrt_mod


D = 26_509_772_707_289
RESIDUES = ((41, 32), (457, 109), (1_414_835_497, 516_876_951))


def gaussian_signs(p):
    root = int(sqrt_mod(-1, p))
    a, b = p, min(root, p - root)
    while b * b > p:
        a, b = b, a % b
    c = isqrt(p - b * b)
    assert b * b + c * c == p
    return tuple(int(prod(legendre_symbol(b + t * y, q) for q, t in RESIDUES))
                 for y in (c, -c))


def predicted_primes(a, t, trace, count):
    # a X² + 2t XY + (t²+D)/a Y², evaluated at Y=1.
    assert (t * t + D) % a == 0
    constant = (t * t + D) // a
    chosen = []
    for x in range(1, 2000):
        p = a * x * x + 2 * t * x + constant
        if isprime(p) and (2 * D) % p != 0:
            chosen.append((a, 2 * t, x, p, trace))
            if len(chosen) == count:
                return chosen
    raise ValueError("Too few represented primes")


def main():
    assert prod(q for q, _ in RESIDUES) == D
    assert gaussian_signs(13) == (-1, -1)
    t = int(sqrt_mod(-D, 13))
    calls = predicted_primes(1, 0, 2, 8) + predicted_primes(13, t, -2, 8)
    assert len({p for _, _, _, p, _ in calls}) == 16
    print("a,b,x,prime,predicted_trace,first_sign,second_sign")
    for a, b, x, p, trace in calls:
        left, right = gaussian_signs(p)
        assert left + right == trace
        print(f"{a},{b},{x},{p},{trace},{left},{right}")


if __name__ == "__main__":
    main()
