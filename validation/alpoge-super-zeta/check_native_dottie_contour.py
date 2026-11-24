"""Certified disk bounds and weighted contour moments for the native Dottie cross-product."""

from math import factorial

from flint import acb, acb_series, arb, ctx


def tail_moment(rate, start, degree):
    """Integral of t**degree * exp(-rate*t) from start to infinity."""
    return (-rate * start).exp() * sum(
        factorial(degree) // factorial(degree - j) * start**(degree-j) / rate**(j+1)
        for j in range(degree + 1)
    )


def complex_error(bound):
    radius = arb(0, bound.abs_upper())
    return acb(radius, radius)


def log_gap(x, analytic):
    """Log of the minus native determinant divided by the plus determinant."""
    sh = x.sinh()
    common = 3 + 4 * (sh**2 + x**2)
    offset = 4 * x * sh
    return ((common - offset) / (common + offset)).log(analytic=analytic)


def integral_coefficients(center, order):
    """Taylor coefficients of the unscaled Mellin gap, in s (where w=2s)."""
    left, right = -90, 6
    tol = arb(2) ** -167
    upper_x = arb(right).exp()
    coefficients = []
    for k in range(order):
        factorial_k = factorial(k)

        def integrand(u, analytic):
            return ((-2 * center * u).exp() * (-2*u)**k / factorial_k
                    * log_gap(u.exp(), analytic))

        # |log_gap(x)| <= (32/3)*x^2 for x <= 1, and
        # |log_gap(x)| <= (256/9)*exp(-x/2) for x >= 0.
        small = (arb(32) / 3) * tail_moment(arb(3) / 2, arb(-left), k)
        large = (arb(256) / 9) * tail_moment(arb(1) / 2, upper_x, k) / (upper_x * upper_x.sqrt())
        endpoint_error = (small + large) * 2**k / factorial_k
        pieces = [acb.integral(integrand, u, u+3, abs_tol=tol, rel_tol=tol)
                  for u in range(left, right, 3)]
        assert all(piece.is_finite() for piece in pieces)
        coefficients.append(sum(pieces, acb(0)) + complex_error(endpoint_error))
    return coefficients


def poly(coefficients, h):
    value = acb(0)
    for coefficient in reversed(coefficients):
        value = value * h + coefficient
    return value


def gap_and_deriv(s, h, coefficients, pi):
    """Enclose W(s) and W'(s), where W=J_- - J_+."""
    order = len(coefficients)
    radius = abs(h).abs_upper()
    if not radius < arb(1) / 8:
        return acb("nan"), acb("nan")
    x = 2 * radius
    # For u <= 0, the weighted kernel is bounded by (32/3)*exp(3u/2).
    # For u >= 0, exp(u) >= u gives (256/9)*exp(-u).
    # Integrating the exponential Taylor remainder gives these two bounds.
    tail = (arb(32)/3)/(arb(3)/2-x)**(order+1) + (arb(256)/9)/(1-x)**(order+1)
    mellin = poly(coefficients, h) + complex_error(x**order * tail)
    derivative = [k * coefficients[k] for k in range(1, order)]
    mellin_prime = poly(derivative, h) + complex_error(2*order*x**(order-1)*tail)
    sin, cos = (pi*s).sin_cos()
    factor = 2 * s * sin / pi
    factor_prime = 2 * sin / pi + 2 * s * cos
    return factor * mellin, factor_prime * mellin + factor * mellin_prime


def common_and_deriv(s, pi):
    w = 2 * s
    log3 = arb(3).log()
    logpi = pi.log()
    power3 = (w*log3).exp()
    scale = (-w*logpi).exp()
    zeta = acb_series([w, 1], prec=2).zeta()
    reference = scale * (power3-1) * zeta[0]
    slope = 2*scale * ((log3*power3-logpi*(power3-1))*zeta[0] + (power3-1)*zeta[1])
    return reference, slope


def main():
    with ctx.workprec(256):
        center = acb(arb(1)/4, arb(7067363)/10**6)
        radius = arb(1)/4096
        pi = arb.pi()
        coefficients = integral_coefficients(center, 14)
        direction = acb(15069, -24342)
        square = acb(arb(0, radius), arb(0, radius))
        gap, gap_prime = gap_and_deriv(center+square, square, coefficients, pi)
        assert abs(gap).abs_lower() > 11708
        assert abs(gap_prime).abs_upper() < 25255
        assert abs(coefficients[0]).abs_lower() > arb(1188)/10**9
        assert all(abs(x).abs_upper() < arb(5)/10**6 for x in coefficients[1:4])
        # Subdivision prevents interval dependency in the zeta derivative
        # from swamping the derivative defect on the whole square at once.
        defect = arb(0)
        tiles = 16
        step = radius / tiles
        for j in range(tiles):
            for k in range(tiles):
                h = acb(arb((2*j+1-tiles)*step, step), arb((2*k+1-tiles)*step, step))
                g, dg = gap_and_deriv(center+h, h, coefficients, pi)
                ref, dr = common_and_deriv(center+h, pi)
                upper = abs(1-(dg*ref+g*dr)/direction).abs_upper()
                assert upper < arb(1)/4
                defect = defect.max(upper)
        assert defect.abs_upper() < arb(35)/1000
        g0, _ = gap_and_deriv(center, acb(0), coefficients, pi)
        assert abs(g0).abs_lower() > 11700
        r0, _ = common_and_deriv(center, pi)
        center_residual = abs(g0*r0/direction)
        assert center_residual.abs_upper() < arb(1)/10**6

        print("Arb bits", ctx.prec, "Mellin Taylor order", len(coefficients))
        print("Center (1/4) + (7067363/1000000)i; radius 1/4096")
        for k, coefficient in enumerate(coefficients[:4]):
            print(f"Normalized Mellin center coefficient {k}", coefficient.str(24))
        print("Correction gap norm at the center >", abs(g0).abs_lower().str(16))
        print("Correction gap norm on disk >", abs(gap).abs_lower().str(16))
        print("Correction gap derivative norm on disk <", abs(gap_prime).abs_upper().str(16))
        print("Cross-product normalized center residual <", center_residual.abs_upper().str(16))
        print("Normalized derivative defect on disk <", defect.abs_upper().str(16),
              f"({tiles**2} covering boxes)")

        def moment(t, analytic, power):
            h = radius * (acb(0, 2) * pi * t).exp()
            s = center+h
            gap, dg = gap_and_deriv(s, h, coefficients, pi)
            if not gap.is_finite() or gap.contains(0):
                return acb("nan")
            ref, dr = common_and_deriv(s, pi)
            if not ref.is_finite() or ref.contains(0):
                return acb("nan")
            c, dc = gap*ref, dg*ref+gap*dr
            return h**(power+1) * (dc/c)

        tolerance = arb(2)**-83
        results = []
        for k in range(2):
            integrand = lambda t, analytic: moment(t, analytic, k)
            pieces = [acb.integral(integrand, arb(j)/16, arb(j+1)/16,
                                   abs_tol=tolerance, rel_tol=tolerance)
                      for j in range(16)]
            assert all(piece.is_finite() for piece in pieces)
            results.append(sum(pieces, acb(0)))
        count, centered_moment = results
        assert (count-1).contains(0) and abs(count-1).abs_upper() < arb(1)/2
        location = center+centered_moment  # the exact count is one
        assert abs(location-center).abs_upper() < radius
        assert location.real.contains(arb(1)/4)
        lower = arb(7067362570867346895228625)/10**24
        upper = arb(7067362570867346895228627)/10**24
        assert lower < location.imag and location.imag < upper
        print("Count integral", count.str(29))
        print("Centered first moment", centered_moment.str(28))
        print("Recovered location", location.str(29))
        print("Certified imaginary interval (7.067362570867346895228625, 7.067362570867346895228627)")
        print("The count and the location come from the contour of C=J_- Z_+ - J_+ Z_-.")


if __name__ == "__main__":
    main()

