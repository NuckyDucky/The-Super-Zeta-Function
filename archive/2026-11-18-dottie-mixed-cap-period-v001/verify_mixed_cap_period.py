"""Verify six marked mixed-period orbits. Python 3.12, python-flint 0.9.0.

Run: python -B verify_mixed_cap_period.py
"""
from fractions import Fraction
from math import gcd, lcm

from flint import acb, arb, ctx, fmpq


def ball(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def certify_p(L):
    # All complex starts |z-1| <= 2r are enclosed by this initial square.
    r = ball("1e-300")
    e = arb(0, (2 * r).upper())
    z = acb(1) + acb(e, e)
    for j in range(1, 320):
        z = (L * (-L * z).exp()).exp()
        if j in (3, 107):
            assert abs(z - 1) > ball("0.939") > r
    # z_320 = exp(b). Keep its direction before taking the next exponential.
    b = L * (-L * z).exp()
    direction = -L.real * b.imag.cos() + L.imag * b.imag.sin()
    assert b.real > ball("1e177")
    assert direction < ball("-0.0437")
    # Re(-L*z_320) = exp(Re b)*direction < -1000.
    assert arb(20).exp() * ball("0.0437") > 1000
    assert abs(L) < 1
    return_bound = (-arb(1000)).exp().expm1()
    assert return_bound < ball("5.076e-435") < r / 4
    # Cauchy on circles of radius r bounds the derivative on the inner disk.
    assert return_bound / r < ball("5.076e-135") < 1
    return direction


def certify_q(L):
    # A shortened decimal center for the radius-0.01 Phase 3K Q disk.
    anchor = acb(ball("0.99959169"), ball("-0.00920827"))
    disk = ball("0.01")
    assert abs(1 - anchor) < disk
    center, radius, derivative = anchor, disk.upper(), arb(1)
    for j in range(1, 321):
        for rate in (L, -L):
            value = (rate * center).exp()
            change = (abs(rate) * radius).upper()
            # exp bounds the derivative; expm1 bounds displacement on the disk.
            scale = (abs(rate) * abs(value) * change.exp()).upper()
            derivative = (derivative * scale).upper()
            mid = value.mid()
            radius = (abs(value - mid) + abs(value) * change.expm1()).upper()
            center = mid
        if j in (64, 160):
            assert abs(center - anchor) > radius + disk
    assert abs(center - anchor) + radius < disk
    assert derivative < 1
    return derivative


def main():
    for bits in (1024, 2048):
        ctx.prec = bits
        for j in (4, 6, 12, 13, 19, 28):
            x = Fraction("4.749479070945369e-8") + Fraction(2*j-33, 32) * Fraction("3e-10")
            L = acb(-ball(x), ball("0.509892982511772"))
            direction = certify_p(L)
            contraction = certify_q(L)
            print(f"{bits} bits  input {j:2d}  direction {direction.str(8)}  Q derivative <= {contraction.str(8)}")
    # F^2=(g_L,g_{-L}); a primitive F-period m has F^2-period m/gcd(m,2).
    paired_square = lcm(321, 320)
    assert paired_square == 102720
    assert [m for m in (paired_square, 2 * paired_square) if m // gcd(m, 2) == paired_square] == [205440]
    print("PASS: scalar primitive periods 321 and 320; primitive F period 205440")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    main()
