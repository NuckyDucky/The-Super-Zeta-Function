"""Enclose positive-part areas for the quartic's signed dyadic prime sum.

Standalone replay. Requires python-flint >= 0.9. Tested with Python 3.12.
"""

from math import isqrt
from flint import arb, ctx, fmpz

DR, DI = -5045155, 1027708
D = DR**2 + DI**2
CONDUCTOR = ((41, 32), (457, 109), (1414835497, 516876951))


def prime_sieve(bound):
    sieve = bytearray(b"\x01") * (bound + 1)
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((bound - p*p) // p + 1)
    return (p for p in range(2, bound + 1) if sieve[p])


def conductor_sign(a, b):
    value = 1
    for p, t in CONDUCTOR:
        value *= int(fmpz(a + t*b).jacobi(p))
    return value


def split_coordinates(p, t):
    # Cornacchia reduction of the two roots of -1 modulo a split prime.
    r, u = p, min(t, p-t)
    while u*u > p:
        r, u = u, r % u
    v = isqrt(p-u*u)
    if u*u + v*v != p:
        raise ArithmeticError(f"failed sum of squares at {p}")
    return u, v


def coefficients(bound):
    result = {}
    for p in prime_sieve(bound):
        if p == 2:
            q, signs, marks = 2, (1,), (conductor_sign(1, 1),)
        elif p % 4 == 3:
            q = p*p
            if q > bound:
                continue
            signs, marks = (int(fmpz(D).jacobi(p)),), (conductor_sign(p, 0),)
        else:
            t = int(fmpz(-1).sqrtmod(p))
            signs = tuple(int(fmpz(DR + k*DI*t).jacobi(p)) for k in (1, -1))
            a, b = split_coordinates(p, t)
            marks = (conductor_sign(a, b), conductor_sign(a, -b))
            q = p
        if sorted(signs) != sorted(marks):
            raise ArithmeticError(f"local character disagreement at {p}")
        n, j = q, 1
        while n <= bound:
            total = sum(v**j for v in signs)
            if total:
                result[n] = (q, total)
            j += 1
            n *= q
    return result


def independent_value(data, x):
    # Direct kernel summation, separate from the sweep of the slope.
    return sum((arb(q).log() * a * ((n - x) if 2*n > x else -n) / n
                for n, (q, a) in data.items() if n <= x), arb(0))


def positive_integral(lo, hi, u, v):
    """Exact integral of the positive part of the affine piece, with weight x^-3/2."""
    if not (u < 0 or u > 0 or u.is_zero()) or not (v < 0 or v > 0 or v.is_zero()):
        raise ArithmeticError(f"unresolved endpoint sign on [{lo}, {hi}]")
    if u < 0 and v < 0:
        return arb(0)
    if u < 0 or v < 0:
        zero = lo - (hi-lo)*u/(v-u)
        if u < 0:
            lo, u = zero, arb(0)
        else:
            hi, v = zero, arb(0)
    s, t = arb(lo).sqrt(), arb(hi).sqrt()
    return 2 * (hi-lo) / (s+t)**2 * (u/s + v/t)


def knot_values(data, knots):
    intercept = slope = arb(0)
    for x in knots:
        if x in data:
            q, a = data[x]
            b = a * arb(q).log()
            intercept += b
            slope -= b / x
        if x % 2 == 0 and x//2 in data:
            q, a = data[x//2]
            b = a * arb(q).log()
            intercept -= 2*b
            slope += b / (x//2)
        yield x, intercept + x*slope


def last_obstruction(data, knots, total, start, j):
    """Last integer Y for which the already measured portion alone exceeds Y^(1/j)."""
    previous, u = None, None
    cumulative = arb(0)
    for x, v in knot_values(data, knots):
        old_area = cumulative
        if previous is not None and previous >= 64:
            cumulative += positive_integral(previous, x, u, v)
        if x >= start:
            residual = total - cumulative - arb(x).root(j)
            if residual < 0:
                if x == start:
                    raise ArithmeticError("first start already below threshold")
                low, high = previous, x
                while high - low > 1:
                    mid = (low+high)//2
                    mid_value = u + (v-u)*(mid-previous)/(x-previous)
                    mass = total-old_area-positive_integral(previous, mid, u, mid_value)
                    diff = mass-arb(mid).root(j)
                    if diff > 0:
                        low = mid
                    elif diff < 0:
                        high = mid
                    else:
                        raise ArithmeticError("unresolved integer threshold comparison")
                return low, high
            if not residual > 0:
                raise ArithmeticError("unresolved knot threshold comparison")
        previous, u = x, v
    raise ArithmeticError("no crossover")


def main():
    ctx.prec = 192
    starts = (1024, 2048, 4096)
    bound = max(starts)**2
    data = coefficients(bound)
    knots = set(starts).union(y*y for y in starts)
    knots.update(data)
    knots.update(2*n for n in data if 2*n <= bound)
    knots.add(64)
    knots = sorted(knots)
    cumulative = arb(0)
    totals = {}
    values = {}
    first_positive = None
    checks = {64, *starts, *(y*y for y in starts)}
    previous = None
    for x, v in knot_values(data, knots):
        if x == 64 and not v < 0:
            raise ArithmeticError("expected strictly negative H_2(64)")
        if previous is not None and previous >= 64:
            cumulative += positive_integral(previous, x, u, v)
            if first_positive is None and v > 0:
                if not u < 0:
                    raise ArithmeticError("expected strict first crossing")
                first_positive = previous - (x-previous)*u/(v-u)
                print(f"First positive crossing after 64 on [{previous}, {x}]: {first_positive.str(24)}")
        if x in checks:
            totals[x] = cumulative
            values[x] = v
        previous, u = x, v

    print(f"192-bit arithmetic, {len(data)} nonzero signed prime powers through {bound}, {len(knots)} knots")
    for x in sorted(checks):
        if not independent_value(data, x).overlaps(values[x]):
            raise ArithmeticError(f"independent direct-kernel check disagrees at {x}")
    if not first_positive > max(starts):
        raise ArithmeticError("lower endpoints exceed first reversal")

    areas = {y: totals[y*y] - totals[y] for y in starts}
    published = {
        1024: "0.1855496250753356 +/- 1e-15",
        2048: "1.3775398138597694 +/- 1e-15",
        4096: "3.4321001520713061 +/- 1e-15",
    }
    for y, interval in published.items():
        if not arb(interval).contains(areas[y]):
            raise ArithmeticError(f"recomputed area at Y={y} disagrees with the reported enclosure")
    for y, area in areas.items():
        print(f"Y={y}: A(Y)={area.str(24)}")
        for j in (32, 8):
            threshold = arb(y).root(j)
            if area > threshold:
                test = "exceeds"
            elif area < threshold:
                test = "below"
            else:
                raise ArithmeticError("ambiguous threshold comparison")
            print(f"  {test} Y^(1/{j})={threshold.str(18)}")
    for y in starts[1:]:
        area = areas[y]
        print(f"Mass added beyond {(y//2)**2} through {y*y}: {(area-areas[y//2]).str(24)}")
        for j in (32, 8):
            crossover = area**j
            if crossover > y:
                if not ((crossover < first_positive) or (crossover > first_positive)):
                    raise ArithmeticError("ambiguous interval endpoint")
                limiting_value = crossover if crossover < first_positive else first_positive
                print(f"  Every real start from {y} to (strictly below) {limiting_value.str(18)} exceeds Y^(1/{j})")
    if not areas[2048] > arb(4096).root(32):
        raise ArithmeticError("old-window projection disagrees with first two windows")
    if not areas[4096] > arb(4096).root(32):
        raise ArithmeticError("old-window projection failed")
    for j in (32, 8):
        last, following = last_obstruction(data, knots, totals[bound], max(starts), j)
        expected_last = {32: 4_762_984, 8: 19_252}[j]
        if (last, following) != (expected_last, expected_last + 1):
            raise ArithmeticError(f"retained-area crossover disagrees for exponent 1/{j}")
        print(f"  The measured part [Y,{bound}] exceeds Y^(1/{j}) through Y={last}; "
              f"at Y={following} that part falls below the threshold.")


if __name__ == "__main__":
    main()
