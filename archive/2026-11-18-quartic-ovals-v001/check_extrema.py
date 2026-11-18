"""Isolate all stationary points in the normalized quartic plot."""
from fractions import Fraction

from flint import acb_poly, arb, ctx, fmpq


# Coefficients in descending powers of x.
COEFFICIENTS = (961000, -1039740, -1810543, 644010, 1813853)
BRACKETS = (
    ("-7.635216282960414", "-7.635216282960413"),
    ("-1.002507038027921", "-1.002507038027920"),
    ("0.0577935101522401", "0.0577935101522402"),
    ("1.4001675625817223", "1.4001675625817224"),
)


def evaluate(coefficients, x):
    value = 0
    for coefficient in coefficients:
        value = value*x + coefficient
    return value


def interval(lower, upper):
    center = (lower+upper)/2
    radius = (upper-lower)/2
    return arb(fmpq(center.numerator, center.denominator),
               fmpq(radius.numerator, radius.denominator))

def bisect(coefficients, lo, hi, steps):
    flo = evaluate(coefficients, lo)
    assert flo*evaluate(coefficients, hi) < 0
    for _ in range(steps):
        mid = (lo+hi)/2
        fmid = evaluate(coefficients, mid)
        if fmid == 0:
            return mid, mid
        if flo*fmid < 0:
            hi = mid
        else:
            lo, flo = mid, fmid
    return lo, hi


def normalized_gap(x):
    return 2*evaluate(COEFFICIENTS, x).sqrt() / (arb(COEFFICIENTS[0]).sqrt()*(1+x*x))


def main():
    if not __debug__:
        raise RuntimeError("This calculation requires Python assertions.")
    ctx.prec = 384
    a, b, c, d, e = COEFFICIENTS
    # This is the numerator from differentiating f(x)/(1+x²)².
    derivative = (-b, 4*a-2*c, 3*b-3*d, 2*c-4*e, d)
    brackets = [(Fraction(lo), Fraction(hi)) for lo, hi in BRACKETS]
    assert all(lo < hi for lo, hi in brackets)
    assert all(left[1] < right[0] for left, right in zip(brackets, brackets[1:]))
    points = []
    for lo, hi in brackets:
        # Four sign changes in disjoint rational intervals account for the degree.
        root = interval(*bisect(derivative, lo, hi, 192))
        points.append((root, normalized_gap(root)))
    maximum = points[2][1]
    minimum = points[3][1]
    for other in (points[0][1], points[1][1], arb(2)):  # gap at infinity
        assert minimum < other < maximum
    print("Four stationary points and directed enclosures for the normalized gap")
    for root, gap in points:
        print(f"x = {root.str(17)}, gap = {gap.str(14)}")
    print("The third point is the global maximum and the fourth is the global minimum.")
    print("Normalized maximum x:", points[2][0].str(65))
    candidate = arb(fmpq(57739531, 10**9))
    assert candidate < points[2][0]
    print("Maximum x minus 0.057739531:", (points[2][0]-candidate).str(25))
    print("Upper ordinate drop at 0.057739531:", ((maximum-normalized_gap(candidate))/2).str(20))

    x_balance = (183 + arb(1259229).sqrt())/930
    print("Positive zero of N(x):", x_balance.str(20))
    print("Normalized minimum to exact unit gap:", (x_balance-points[3][0]).str(13))
    for root in acb_poly(list(reversed(COEFFICIENTS))).roots(tol=1e-40, maxprec=384):
        print("Complex branch point:", root.str(20))


if __name__ == "__main__":
    main()
