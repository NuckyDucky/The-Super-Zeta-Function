"""Compare the two Mellin formulas at unit coupling and s = (3+i)/4.

With E(v) = cos(sqrt(v))² - v, integrate the full logarithmic derivative on
the negative ray. Separately integrate the relative logarithm and add the
double half-integer reference spectrum evaluated with Riemann zeta. The
two integral formulas agree on 1/2 < Re(s) < 1. The bare relative integral
converges for Re(s) < 1. FLINT encloses one nonreal point in their overlap.

Each integral is taken in y = log(t), split into width-four panels between
-192 and 192. The positive real logarithm on the integration ray fixes
the branch. The complex-ball integration callback checks that its analytic
extension stays on the same branch. All interval output is rounded outwards.
"""
from flint import acb, arb, ctx

LOG_CUTOFF = 192
PANEL_WIDTH = 4
PRECISION_BITS = 192


def hyperbolic_factors(y):
    # q = exp(-2 sqrt(t)) keeps the formulas finite even on the final panel.
    root = (y / 2).exp()
    t = y.exp()
    q = (-2 * root).exp()
    sech_squared = 4 * q / (1 + q) ** 2
    return root, t, q, sech_squared


def integrate_with_tails(integrand, tail):
    total = acb(0)
    tolerance = arb(2) ** -118
    for left in range(-LOG_CUTOFF, LOG_CUTOFF, PANEL_WIDTH):
        total += acb.integral(
            integrand, left, left + PANEL_WIDTH,
            abs_tol=tolerance, rel_tol=tolerance, eval_limit=4000,
        )
    if not total.is_finite():
        raise ArithmeticError("Quadrature failed to enclose an integration panel")
    # A modulus bound for the omitted tails bounds both Cartesian components.
    error = arb(0, tail.upper())
    return total + acb(error, error)


def main():
    ctx.prec = PRECISION_BITS
    s = acb(arb(3) / 4, arb(1) / 4)
    sigma = s.real
    pi = arb.pi()

    def full(y, analytic):
        root, t, q, sech_squared = hyperbolic_factors(y)
        tanh = (1 - q) / (1 + q)
        derivative = (tanh / root + sech_squared) / (1 + t * sech_squared)
        return ((1 - s) * y).exp() * derivative

    def relative(y, analytic):
        _, t, _, sech_squared = hyperbolic_factors(y)
        v = t * sech_squared
        if analytic and not (1 + v).real > 0:
            return acb("nan")
        return (-s * y).exp() * v.log1p()

    # For 0<t<=1: 0<=d log(E(-t))/dt<=2, and log(1+t sech²(sqrt t))<=t.
    # For t>=1 the derivative is <=2/sqrt(t): tanh(x)<=1 and
    # x sech²(x)<=4x exp(-2x)<=4/e²<1 for x=sqrt(t)>=1.
    # The relative log is <=4 because x² exp(-2x)<=1. Integrating these
    # majorants over t<exp(-Y) and t>exp(Y) gives the bounds below.
    Y = LOG_CUTOFF
    lower = (-(1 - sigma) * Y).exp() / (1 - sigma)
    upper = sigma - arb(1) / 2
    full_tail = 2 * lower + 2 * (-upper * Y).exp() / upper
    relative_tail = lower + 4 * (-sigma * Y).exp() / sigma

    factor = (pi * s).sin() / pi
    spectral = factor * integrate_with_tails(full, full_tail)
    correction = s * factor * integrate_with_tails(relative, relative_tail)
    reference = 2 * acb(pi) ** (-2 * s) * (acb(2) ** (2 * s) - 1) * (2 * s).zeta()
    reconstructed = reference + correction
    residual = spectral - reconstructed
    if not residual.is_finite() or not (0 in residual):
        raise ArithmeticError("The two enclosures are disjoint or unresolved")
    if not (abs(residual.real) < arb("2e-20") and abs(residual.imag) < arb("2e-20")):
        raise ArithmeticError("The difference enclosure is too wide to resolve the comparison")

    print(f"s = (3+i)/4, epsilon = 1, precision = {PRECISION_BITS} bits")
    print("Full log-derivative integral, including its sine prefactor:", spectral)
    print("Relative integral, including its prefactor, plus reference:", reconstructed)
    print("Full minus reconstructed:", residual)
    print("Two-tail bounds on the integrals before their prefactors:", full_tail, relative_tail)


if __name__ == "__main__":
    main()
