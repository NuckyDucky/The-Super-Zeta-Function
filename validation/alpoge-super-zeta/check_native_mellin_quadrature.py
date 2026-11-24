"""Directed finite quadrature for the four actual Dottie correction moments."""

from fractions import Fraction
from math import factorial

from flint import acb, arb, ctx


NUMERATORS = (
    -4096, -4061, -3956, -3784, -3547, -3250, -2896, -2493, -2048,
    -1567, -1060, -535, 0, 535, 1060, 1567, 2048, 2493, 2896, 3250,
    3547, 3784, 3956, 4061, 4096,
)
NODES = tuple(Fraction(n, 4096) for n in NUMERATORS)


def interpolation_weights():
    """Integrate the rational Lagrange basis exactly on [-1, 1]."""
    weights = []
    for j, node in enumerate(NODES):
        poly = [Fraction(1)]
        denominator = Fraction(1)
        for k, other in enumerate(NODES):
            if j == k:
                continue
            next_poly = [Fraction(0)] * (len(poly) + 1)
            for n, coefficient in enumerate(poly):
                next_poly[n] -= other * coefficient
                next_poly[n + 1] += coefficient
            poly = next_poly
            denominator *= node - other
        weights.append(sum(2 * coefficient / (n + 1)
                           for n, coefficient in enumerate(poly) if n % 2 == 0)
                       / denominator)
    assert all(weight > 0 for weight in weights)
    for k in range(len(NODES)):
        assert sum(w * x**k for w, x in zip(weights, NODES)) == Fraction(
            1 - (-1)**(k + 1), k + 1)
    return tuple(weights)


def exact(x):
    return arb(x.numerator) / x.denominator


def kernel_value(u, *, analytic=False):
    """Scaled determinant logs times exp(-2*firstCenter*u)."""
    x = u.exp()
    b = (-x).exp()
    t = 1 - b*b
    a = t*t + (3 + 4*x*x)*b*b
    off = 2*x*b*t
    minus, plus = a - off, a + off
    if analytic and not (minus.real > 0 and plus.real > 0):
        return None
    assert minus.real > 0 and plus.real > 0
    s = acb(arb(1)/4, arb(7067363)/10**6)
    return (-2*s*u).exp() * (minus.log(analytic=True) - plus.log(analytic=True))


def panels(lo, hi):
    """Cover [lo,hi] by panels whose enlarged disks stay in the log domain."""
    c, h = (lo + hi)/2, (hi - lo)/2
    radius = 8*h
    u = acb(arb(exact(c), exact(radius)), arb(0, exact(radius)))
    value = kernel_value(u, analytic=True)
    if value is not None:
        yield c, h, abs(value).abs_upper(), abs(2*u).abs_upper()
        return
    assert h >= Fraction(1, 2**16), (c, h)
    yield from panels(lo, c)
    yield from panels(c, hi)


def main():
    ctx.prec = 192
    weights = interpolation_weights()
    assert sum(weights) == 2
    scaled_nodes = tuple((exact(node), exact(weight)) for node, weight in zip(NODES, weights))
    moments = [acb(0) for _ in range(4)]
    errors = [arb(0) for _ in range(4)]
    panel_count = 0
    for j in range(-32*32, 5*32):
        for center, h, norm_bound, moment_scale in panels(Fraction(j, 32), Fraction(j+1, 32)):
            panel_count += 1
            d = exact(h)
            for node, weight in scaled_nodes:
                u = acb(exact(center) + d*node)
                weighted = d*weight*kernel_value(u)
                for k in range(4):
                    moments[k] += weighted
                    weighted *= (-2*u)/(k+1)
            for k in range(4):
                # On the disk of radius 8*h, the k-th integrand is bounded
                # by norm_bound*moment_scale**k/k!. The exact degree-24
                # rule and Cauchy's estimate give this absolute error.
                errors[k] += (4*d*norm_bound*moment_scale**k/factorial(k)
                              * (arb(1)/8)**len(NODES)/(1-arb(1)/8))
    print(f"Arb bits {ctx.prec}. Panels {panel_count}. Nodes per panel {len(NODES)}.")
    print("Rational node rule verified to degree 24 with positive weights of sum 2.")
    bounds = []
    for k, value in enumerate(moments):
        err = errors[k].abs_upper()
        box = value + acb(arb(0, err), arb(0, err))
        bounds.append(box)
        print(f"Finite coefficient {k} {box.str(22)}")
        print(f"    Cauchy quadrature error {err.str(12)}")
    assert bounds[0].real < -arb(11565)/10**10
    assert bounds[0].imag < -arb(2740)/10**10
    assert all(abs(v.real) < arb(271)/10**8 and abs(v.imag) < arb(405)/10**8
               for v in bounds[1:])
    print("All eight finite inputs for firstDisk_correctionGap_lower_of_finite pass.")


if __name__ == "__main__":
    main()
