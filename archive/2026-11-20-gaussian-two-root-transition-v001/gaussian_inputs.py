"""Frozen Dottie height, conductor characters and Gaussian prime-ideal enumeration."""
from math import isqrt, prod
from flint import arb, fmpq


def height():
    ratio = fmpq(4749479070945369, 10**23) / fmpq(509892982511772, 10**15)
    return arb.pi() / (80 * arb(ratio**2).log1p())


LIMIT = 100000
CONDUCTOR = ((41, 32), (457, 109), (1414835497, 516876951))
Q = 4 * prod(p for p, _ in CONDUCTOR)


def sign(m, n):
    values = (pow((m + n*t) % p, (p-1)//2, p) for p, t in CONDUCTOR)
    return prod(-1 if v > 1 else v for v in values)


def prime_ideals(bound):
    sieve = bytearray([1]) * (bound+1)
    for n in range(2, isqrt(bound)+1):
        if sieve[n]:
            sieve[n*n:bound+1:n] = bytes((bound-n*n)//n+1)
    gaussian = []
    primes = [p for p in range(2, bound+1) if sieve[p]]
    for p in primes:
        if p == 2:
            gaussian.append((p, sign(1, 1)))
        elif p % 4 == 3:
            if p*p <= bound:
                gaussian.append((p*p, sign(p, 0)))
        else:
            for b in range(1, isqrt(p//2)+1):
                a = isqrt(p-b*b)
                if a*a+b*b == p:
                    gaussian.extend(((p, sign(a, b)), (p, sign(a, -b))))
                    break
            else:
                raise ArithmeticError(f"Missing split generators at {p}")
    return primes, gaussian
