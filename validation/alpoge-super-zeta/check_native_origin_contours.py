"""Separate the three cross-product zeros at s=0 by their source."""

from flint import acb, acb_series, arb, ctx

from check_native_dottie_contour import (
    complex_error,
    gap_and_deriv,
    integral_coefficients,
    poly,
    unscaled_and_deriv,
)


def factor_and_deriv(s, pi):
    log_pi = pi.log()
    log_three = arb(3).log()
    scale = (-2*s*log_pi).exp()
    shifted = (2*s*log_three).expm1()
    return scale*shifted, 2*scale*(log_three*(1+shifted)-log_pi*shifted)


def zeta_and_deriv(s, coefficients, cauchy_radius, cauchy_bound):
    """Taylor enclosures for zeta(2*s) and its derivative in s."""
    w = 2*s
    q = abs(w).abs_upper()/cauchy_radius
    if not q < 1:
        return acb("nan"), acb("nan")
    order = len(coefficients)
    error = cauchy_bound*q**order/(1-q)
    slope_error = (cauchy_bound/cauchy_radius)*q**(order-1) * (
        1/(1-q)**2 + (order-1)/(1-q)
    )
    derivative = [k*coefficients[k] for k in range(1, order)]
    return (poly(coefficients, w) + complex_error(error),
            2*(poly(derivative, w) + complex_error(slope_error)))


def main():
    with ctx.workprec(256):
        r = arb(1)/128
        pi = arb.pi()
        m = integral_coefficients(acb(0), 18)
        order = 32
        ctx.cap = order
        coefficients = acb_series([0, 1], prec=order).zeta().coeffs()
        assert len(coefficients) == order
        # zeta is holomorphic on the w-disk of radius 1/4. Its absolute
        # bound on the enclosing square controls every Taylor coefficient.
        cauchy_radius = arb(1)/4
        cauchy_square = acb(arb(0, cauchy_radius), arb(0, cauchy_radius))
        cauchy_bound = arb(370)
        assert abs(cauchy_square.zeta()).abs_upper() < cauchy_bound
        square = acb(arb(0, r), arb(0, r))
        mellin, _ = unscaled_and_deriv(square, m, arb(0))
        ordinary, _ = zeta_and_deriv(square, coefficients, cauchy_radius, cauchy_bound)
        assert abs(mellin).abs_lower() > 1
        assert abs(ordinary).abs_lower() > arb(2)/5
        # The only sine zero on the disk is 0. The zeros of the expm1
        # factor are at 2*s*log(3) = 2*pi*i*k, so only k=0 is possible here.
        assert r < 1 and 2*r*arb(3).log() < 2*pi

        def density(t, analytic, channel):
            s = r * (acb(0, 2) * pi * t).exp()
            gap, gap_prime = gap_and_deriv(s, s, m, pi, arb(0))
            factor, factor_prime = factor_and_deriv(s, pi)
            z, dz = zeta_and_deriv(s, coefficients, cauchy_radius, cauchy_bound)
            if channel == "cross-product":
                f = gap * factor * z
                df = gap_prime * factor * z + gap * factor_prime * z + gap * factor * dz
            elif channel == "correction gap":
                f, df = gap, gap_prime
            elif channel == "arithmetic prefactor":
                f, df = factor, factor_prime
            else:
                f, df = z, dz
            if not f.is_finite() or f.contains(0):
                return acb("nan")
            return s*df/f

        print("Arb bits", ctx.prec, "Mellin Taylor order", len(m), "zeta Taylor order", order)
        print("Center 0; radius 1/128")
        print("Normalized gap norm on disk >", abs(mellin).abs_lower().str(16))
        print("Ordinary zeta norm on disk >", abs(ordinary).abs_lower().str(16))
        counts = {}
        for channel, exact in [("cross-product", 3), ("correction gap", 2),
                               ("arithmetic prefactor", 1), ("ordinary zeta", 0)]:
            def integrand(t, analytic):
                return density(t, analytic, channel)

            tolerance = arb(2)**-68
            parts = [acb.integral(integrand, arb(j)/16, arb(j+1)/16,
                                  abs_tol=tolerance, rel_tol=tolerance) for j in range(16)]
            assert all(piece.is_finite() for piece in parts)
            count = sum(parts, acb(0))
            assert (count-exact).contains(0) and abs(count-exact).abs_upper() < arb(1)/2
            counts[channel] = count
            print(channel, count.str(20))
        signed = counts["cross-product"] - counts["correction gap"] - counts["arithmetic prefactor"]
        assert signed.contains(0) and abs(signed).abs_upper() < arb(1)/2
        print("Cross minus gap minus prefactor", signed.str(20))


if __name__ == "__main__":
    main()

