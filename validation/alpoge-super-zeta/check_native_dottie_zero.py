"""Arb enclosures of the two native Mellin corrections at the same zeta zero."""

from flint import acb, acb_series, arb, ctx


def native_integral(w, sine_sign, derivative):
    """Return the integral in log-ray coordinate, including both omitted tails."""
    def integrand(u, analytic):
        x = u.exp()
        sh = x.sinh()
        q = 4 * x * (x - sine_sign * sh) / (3 + 4 * sh**2)
        value = (-w * u).exp() * (1 + q).log(analytic=analytic)
        return -2 * u * value if derivative else value

    # On 0 < x <= 1, sinh(x) <= x*sinh(1) < 2*x by its positive
    # power series, and |K(x)| <= (16/3)*x^2 by the log-ratio bound.
    # Lean's other bound is |K(x)| <= (128/9)*exp(-x/2) for x >= 0.
    # On the critical line the measure in the x coordinate has |x^-w-1| = x^-3/2.
    start, finish = -90, 6
    exponent = arb(3) / 2
    small = (arb(16) / 3) * (exponent * start).exp() / exponent
    x_end = arb(finish).exp()
    large = (arb(256) / 9) * (-x_end / 2).exp() / (x_end * x_end.sqrt())
    if derivative:
        # At the small end integrate 2*|u|*exp(3u/2). At the large end
        # use 2*log(x) <= 2*x for x >= exp(6).
        small *= 2 * (-start + 1 / exponent)
        large *= 2 * x_end

    tol = arb(2) ** -175
    pieces = [
        acb.integral(integrand, u, u + 3, rel_tol=tol, abs_tol=tol)
        for u in range(start, finish, 3)
    ]
    assert all(piece.is_finite() for piece in pieces)
    tail = arb(0, (small + large).abs_upper())
    return sum(pieces, acb(0)) + acb(tail, tail)


def main():
    with ctx.workprec(256):
        w = acb.zeta_zero(1)
        assert w.real == arb("0.5")
        s = w / 2
        pie = arb.pi()
        prefactor = 2 * s * (pie * s).sin() / pie
        prefactor_prime = 2 * (pie * s).sin() / pie + 2 * s * (pie * s).cos()
        zeta_jet = acb_series([w, 1], prec=2).zeta()
        assert zeta_jet[0].contains(0) and not zeta_jet[1].contains(0)
        reference_prime = 2 * ((-w * pie.log()).exp()) * ((w * arb(3).log()).expm1()) * zeta_jet[1]

        print("Arb precision", ctx.prec)
        print("s0", s.str(32))
        print("R'(s0)", reference_prime.str(30))
        corrections = []
        derivatives = []
        for sign, angle in [(1, "-pi/6"), (-1, "+pi/6")]:
            value = native_integral(w, sign, False)
            derivative = native_integral(w, sign, True)
            j = prefactor * value
            jp = prefactor_prime * value + prefactor * derivative
            assert not j.contains(0) and j.rel_accuracy_bits() >= 100
            assert jp.rel_accuracy_bits() >= 100
            corrections.append(j)
            derivatives.append(jp)
            print(angle, "J(s0)", j.str(30))
            print(angle, "J'(s0)", jp.str(30))
            print(angle, "Z'(s0)", (reference_prime + jp).str(30))
        diff = corrections[1] - corrections[0]
        assert not diff.contains(0) and diff.rel_accuracy_bits() >= 100
        print("Z_+ - Z_-", diff.str(30))
        print("(Z_+ - Z_-)'", (derivatives[1] - derivatives[0]).str(30))
        ratio = corrections[1] / corrections[0]
        cross_prime = -diff * reference_prime
        ratio_gap_prime = cross_prime / corrections[0]**2
        assert not cross_prime.contains(0) and cross_prime.rel_accuracy_bits() >= 100
        assert not ratio_gap_prime.contains(0) and ratio_gap_prime.rel_accuracy_bits() >= 100
        print("J_+/J_- at the zero", ratio.str(30))
        print("(J_- Z_+ - J_+ Z_-)'", cross_prime.str(30))
        print("(Z_+/Z_- - J_+/J_-)'", ratio_gap_prime.str(30))
        print("Both native values and their difference are nonzero on this zero ball.")


if __name__ == "__main__":
    main()
