"""Directed finite quadrature for the four actual Dottie correction moments."""

from argparse import ArgumentParser
from fractions import Fraction
from math import factorial

from flint import acb, arb, ctx


NUMERATORS = (
    -4096, -4061, -3956, -3784, -3547, -3250, -2896, -2493, -2048,
    -1567, -1060, -535, 0, 535, 1060, 1567, 2048, 2493, 2896, 3250,
    3547, 3784, 3956, 4061, 4096,
)
NODES = tuple(Fraction(n, 4096) for n in NUMERATORS)
UNIFORM_NODE_DENOMINATOR = 128 * 4096
SAMPLE_SCALE = 10**14


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


def panel_specs(uniform):
    if uniform:
        for i in range(2368):
            yield Fraction(-32) + Fraction(2*i + 1, 128), Fraction(1, 128), None, None
    else:
        for j in range(-32*32, 5*32):
            yield from panels(Fraction(j, 32), Fraction(j+1, 32))


def rounded_sample(value):
    """Pick a grid value and check its distance from the full Arb enclosure."""
    midpoint_index = (value.mid() * SAMPLE_SCALE + arb(1)/2).floor().unique_fmpz()
    index = int(midpoint_index)
    assert abs(value - arb(index)/SAMPLE_SCALE) < arb(1)/SAMPLE_SCALE
    return index


def check_rational_moments(totals, weights):
    # Separate the node column weights from the integer sums over panels.
    moments = tuple(tuple(
        sum(w * total for w, total in zip(weights, row))
        / (128 * SAMPLE_SCALE * UNIFORM_NODE_DENOMINATOR**k * factorial(k))
        for k, row in enumerate(component_rows)
    ) for component_rows in totals)
    real, imaginary = moments
    assert real[0] <= -Fraction(11567, 10**10)
    assert imaginary[0] <= -Fraction(27415, 10**11)
    assert all(abs(v) <= Fraction(268, 10**8) for v in real[1:])
    assert all(abs(v) <= Fraction(402, 10**8) for v in imaginary[1:])
    for k, (r, i) in enumerate(zip(real, imaginary)):
        print(f"Rational weighted sum {k} {exact(r).str(22)} + {exact(i).str(22)}j")
    print("All node-to-rational distances are below 10^-14 (directed Arb).")
    print("All eight rational sum inequalities pass (exact Python fractions).")


def main(uniform=False):
    ctx.prec = 192
    weights = interpolation_weights()
    assert sum(weights) == 2
    scaled_nodes = tuple((exact(node), exact(weight)) for node, weight in zip(NODES, weights))
    moments = [acb(0) for _ in range(4)]
    errors = [arb(0) for _ in range(4)]
    rational_totals = [[[0] * len(NODES) for _ in range(4)] for _ in range(2)] if uniform else None
    panel_count = 0
    for center, h, norm_bound, moment_scale in panel_specs(uniform):
        panel_count += 1
        d = exact(h)
        for j, (node, weight) in enumerate(scaled_nodes):
            u = acb(exact(center) + d*node)
            value = kernel_value(u)
            weighted = d*weight*value
            if rational_totals is not None:
                numerator = int(center * UNIFORM_NODE_DENOMINATOR) + NUMERATORS[j]
                for side, component in enumerate((value.real, value.imag)):
                    rounded = rounded_sample(component)
                    for k, row in enumerate(rational_totals[side]):
                        row[j] += rounded * (-2*numerator)**k
            for k in range(4):
                moments[k] += weighted
                weighted *= (-2*u)/(k+1)
        if not uniform:
            for k in range(4):
                # On the disk of radius 8*h, the k-th integrand is bounded
                # by norm_bound*moment_scale**k/k!. The exact degree-24
                # rule and Cauchy's estimate give this absolute error.
                errors[k] += (4*d*norm_bound*moment_scale**k/factorial(k)
                              * (arb(1)/8)**len(NODES)/(1-arb(1)/8))
    if uniform:
        for k in range(4):
            majorant = Fraction(66**k, factorial(k)) * Fraction(11, 4)**17 * Fraction(8, 3)
            error = Fraction(37*4, 2) * majorant * Fraction(1, 8)**len(NODES) / Fraction(7, 8)
            errors[k] = exact(error)
    print(f"Arb bits {ctx.prec}. Panels {panel_count}. Nodes per panel {len(NODES)}.")
    print("Rational node rule verified to degree 24 with positive weights of sum 2.")
    if uniform:
        for k, value in enumerate(moments):
            print(f"Fixed-partition weighted sum {k} {value.str(22)}")
        assert moments[0].real < -arb(11566)/10**10 and moments[0].imag < -arb(2741)/10**10
        assert all(abs(v.real) < arb(270)/10**8 and abs(v.imag) < arb(404)/10**8
                   for v in moments[1:])
        print("All eight inputs for firstDisk_correctionGap_lower_of_quadrature pass.")
        check_rational_moments(rational_totals, weights)
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
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--uniform-strip", action="store_true", help="use the fixed Lean partition and analytic strip bound")
    main(uniform=parser.parse_args().uniform_strip)
