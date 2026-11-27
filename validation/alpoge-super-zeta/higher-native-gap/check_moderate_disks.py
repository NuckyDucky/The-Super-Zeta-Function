"""Directed Arb enclosures for the actual native Dottie correction gap."""

from math import factorial

from flint import acb, arb, ctx


def coefficient(w, degree, left=-45, right=6):
    """Coefficient of h**degree in the log-ray gap at ordinary input w+h."""
    def integrand(u, analytic):
        x = u.exp()
        b = (-x).exp()
        t = 1 - b**2
        a = t**2 + (3 + 4 * x**2) * b**2
        offset = 2 * x * b * t
        gap = ((a - offset) / (a + offset)).log(analytic=analytic)
        return (-w * u).exp() * gap * (-u)**degree / factorial(degree)

    sigma = w.real
    alpha = 2 - sigma
    small_tail = (arb(32) / 3) * (alpha * left).exp() * sum(
        arb(-left)**j / (factorial(j) * alpha**(degree + 1 - j))
        for j in range(degree + 1)
    )
    assert right >= 6
    large_tail = (
        (arb(256) / 9) * (-arb(right).exp() / 4).exp()
        / (1 + sigma)**(degree + 1)
    )
    tolerance = arb(2)**-118
    pieces = [
        acb.integral(
            integrand, u, u + 3, rel_tol=tolerance, abs_tol=tolerance
        )
        for u in range(left, right, 3)
    ]
    assert all(piece.is_finite() for piece in pieces)
    error = arb(0, (small_tail + large_tail).abs_upper())
    return sum(pieces, acb(0)) + acb(error, error)


def check_disk(w, radius, coefficients, claimed):
    sigma = w.real
    order = len(coefficients)
    # The pointwise exponential remainder is exp(r|u|)*(r|u|)^order/order!.
    # The log-gap bounds are (32/3)e^(2u) for u<=0 and (256/9)e^(-u)
    # for u>=0, using exp(u)/2 >= u in the second one.
    remainder = radius**order * (
        (arb(32) / 3) / (2 - sigma - radius)**(order + 1)
        + (arb(256) / 9) / (1 + sigma - radius)**(order + 1)
    )
    variation = sum(
        value.abs_upper() * radius**degree
        for degree, value in enumerate(coefficients[1:], start=1)
    ) + remainder
    mellin_lower = coefficients[0].abs_lower() - variation
    assert mellin_lower > 0
    height_lower = w.imag - radius
    pi = arb.pi()
    factor_lower = height_lower * (pi * height_lower / 2).sinh() / pi
    gap_lower = mellin_lower * factor_lower
    print("Ordinary center", w.str(28), "ordinary radius", radius.str(14))
    print("Spectral center", (w / 2).str(28), "spectral radius", (radius / 2).str(14))
    print("Center normalized Mellin gap", coefficients[0].str(27))
    print("Center ordinary derivative of normalized Mellin gap", coefficients[1].str(27))
    print("Complex variation upper bound", variation.abs_upper().str(13))
    print("Taylor remainder upper bound", remainder.abs_upper().str(13))
    print("Raw gap magnitude lower bound", gap_lower.str(17))
    assert gap_lower > claimed
    print("Checked raw gap >", claimed, flush=True)


def main():
    ctx.prec = 192
    ctx.threads = 1
    print("Arb precision", ctx.prec, flush=True)
    for ordinal, height, archived_bound, enlarged_bound in (
        (2, "21.02203963877155499", 1702200, 1699800),
        (3, "25.0108575801456888", 28273600, 28233500),
    ):
        # Exact rounded decimal centers of the archived terminal root balls.
        w = acb(arb(1) / 2, arb(height))
        coefficients = [coefficient(w, k) for k in range(6)]
        zero = acb.zeta_zero(ordinal)
        for radius, bound in (
            (arb("1e-8"), archived_bound),
            (arb(1) / 2048, enlarged_bound),
        ):
            assert (zero - w).abs_upper() < radius
            check_disk(w, radius, coefficients, bound)


if __name__ == "__main__":
    main()
