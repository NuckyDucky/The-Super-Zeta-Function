"""Directed bounds for the smoothed prime sum of Q(sqrt(-3)), python-flint 0.9.0.

Run with Python from any directory to print JSON. The previous experiment's
integer recursion and an independent prime sieve are reused. This file uses
the Dedekind logarithmic derivative and its corresponding pole subtraction.
"""

import json
from array import array
from math import isqrt


from flint import acb_series, arb, ctx, dirichlet_char, fmpq

def advance(tape, active):
    """Recover (M,2M] all at once using only nonunit entries at d<=M."""
    m = len(tape) - 1
    odd_product = array("I", [1]) * m
    even_product = array("I", [1]) * m
    for d in active:
        old_value = tape[d]
        first = m // d + 1
        for parity, product in ((1, odd_product), (0, even_product)):
            k = first + ((first - parity) % 2)
            for i in range(k*d - m - 1, m, 2*d):
                product[i] *= old_value
    new = array("I")
    next_active = []
    for i, (odd, even) in enumerate(zip(odd_product, even_product)):
        n = m + i + 1
        if n % 2:
            numerator, denominator = n * even, odd
        else:
            numerator, denominator = 4 * even, n * odd
        q, remainder = divmod(numerator, denominator)
        if remainder or q < 1:
            raise ArithmeticError(f"Noninteger factorial update at {n}")
        new.append(q)
        if q > 1:
            next_active.append(n)
    tape.extend(new)
    active.extend(next_active)


def floor_cuberoot(n):
    lo, hi = 0, 1 << ((n.bit_length() + 2) // 3)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**3 <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi**3 == n else lo


def prime_power_bases(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p * p :: p] = bytes((limit - p * p) // p + 1)
    bases = {}
    for p in range(2, limit + 1):
        if prime[p]:
            power = p
            while power <= limit:
                bases[power] = p
                power *= p
    return bases


def field_constants():
    chi = dirichlet_char(3, 2)
    assert [chi(n) for n in (0, 1, 2)] == [0, 1, -1]
    jet = acb_series([1, 1], 2).dirichlet_l(chi)
    c = (jet[1] / jet[0]).real
    third = arb(1) / 3
    gamma = arb.const_euler()
    assert c.overlaps(gamma + (2*arb.pi()).log()
                      - 3*(third.lgamma() - (2*third).lgamma()))
    return 1 + gamma + c, 2 + (3 / (4 * arb.pi()**2)).log() + 2*c


def field_weights_match_residue_polynomial(sieve):
    # The ring of integers is Z[omega] with omega^2+omega+1=0. Over F_p,
    # root counts 0, 1, 2 distinguish inert, ramified, and split primes.
    for p in range(2, 258):
        if sieve.get(p, 1) != p:
            continue
        roots = sum((r*r+r+1) % p == 0 for r in range(p))
        for m in range(1, 7):
            field_weight = roots if roots or m % 2 else 2
            assert field_weight == 1 + (0, 1, -1)[pow(p, m, 3)]


def calculate_windows():
    # The anchor is 2**18. Four doublings reach the fixed endpoint 2**22.
    windows = []
    for k in range(5):
        hi = 1 << (18 + k)
        theta = fmpq(1, 2) + fmpq(1, 20 << k)
        windows.append(dict(lo=floor_cuberoot(hi**2), hi=hi, knots=0,
            tests=[dict(theta=t, upper=arb(0)) for t in (theta, fmpq(1, 2))]))

    tape, active = array('I', [0, 1]), []
    while len(tape)-1 < windows[-1]['hi']:
        advance(tape, active)
    slopesum, _ = field_constants()
    intercept = arb(0)
    knots = sorted(set(active).union(n for win in windows for n in (win['lo'], win['hi'])))
    for n in knots:
        log_n = arb(n).log()
        q = tape[n]
        if q > 1:
            weight = (log_n if q == n else arb(q).log()) * (1+(0, 1, -1)[n % 3])
            slopesum += weight/n
            intercept -= weight
        if n < windows[0]['lo']:
            continue
        g = n*(slopesum-log_n)+intercept
        for win in windows:
            if not win['lo'] <= n <= win['hi']:
                continue
            for test in win['tests']:
                power = (log_n*test['theta']).exp()
                ratio = g/power
                if 'last' in test:
                    left, power_left, ratio_left = test['last']
                    # G''(x)=-1/x in a knot gap. The chord error is bounded by
                    # (n-left)^2/(8*left). x^theta is positive and concave.
                    slack = (n-left)**2/(8*left*power_left)
                    cap = ratio.max(ratio_left).max(arb(0)) + slack
                    test['upper'] = test['upper'].max(cap)
                test['last'] = (n, power, ratio)
            win['knots'] += 1
    sieve = prime_power_bases(len(tape)-1)
    for n in range(1, len(tape)):
        if tape[n] != sieve.get(n, 1):
            raise ArithmeticError(f'Coefficient mismatch at {n}')
    field_weights_match_residue_polynomial(sieve)
    return windows, len(tape)-1


def main():
    if not __debug__:
        raise RuntimeError('Run the checker with Python assertions enabled.')
    ctx.prec = 160
    windows, cutoff = calculate_windows()
    result = dict(field='Q(sqrt(-3))', window_bits=ctx.prec,
        independent_prime_power_checks=cutoff,
        residue_polynomial_check='every prime <= 257, powers 1 through 6', windows=[])
    for win in windows:
        result['windows'].append(dict(lower=win['lo'], upper_endpoint=win['hi'], knots=win['knots'],
            bounds=[dict(exponent=str(q['theta']), upper=q['upper'].upper().str(18),
                passes=bool(q['upper'] < 1)) for q in win['tests']]))
    assert all(win['tests'][1]['upper'] < fmpq(65597, 1000000) for win in windows[1:])
    ctx.prec = 192
    _, k = field_constants()
    result['conditional_limsup_bits'] = ctx.prec
    result['conditional_limsup'] = k.str(36)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
