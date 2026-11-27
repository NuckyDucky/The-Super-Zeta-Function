"""Enclose the weighted ordinary-zeta reading on the entire Cayley example.

Use a single zeta polynomial for all arcs. If d_k are the Taylor coefficients
at the disk center c and h is the sampling radius, the discrete Fourier
coefficient b_k is sum_{l >= 0} d_{k+l*N} h**(k+l*N), for 0 <= k < N.
Cauchy's coefficient bound on the larger disk controls both that alias
sum and the remainder of the polynomial on the measuring circle.
"""

import json

import flint
from flint import acb, arb, ctx


HEIGHT = 100000001
SAMPLE_COUNT = 96
DEGREE = 64


def zeta_polynomial(center: acb, radius: arb) -> tuple[arb, list[acb], arb]:
    """Return the sample radius, the power basis in (w-c)/h, and its error."""
    outer = arb(1) / 2
    h = arb(5) / 16
    if not (0 < radius < h < outer):
        raise ArithmeticError("The measuring, sampling, and Cauchy radii must be nested.")

    # DLMF 25.2.8 with N=1 gives |zeta(w)| <= 1 + 1/|w-1| + |w|/Re(w).
    # On the closed Cauchy disk, Re(w) >= 1/4, |w-1| > 1, |w| <= T + 5/4.
    cauchy_bound = arb(10**9)
    min_real = center.real - outer
    min_pole_distance = abs(center - 1) - outer
    if not (min_real > 0 and min_pole_distance > 1):
        raise ArithmeticError("The Cauchy disk left the domain of the majorant.")
    if not (1 + 1 / min_pole_distance + (abs(center) + outer) / min_real < cauchy_bound):
        raise ArithmeticError("The Cauchy modulus bound was not enclosed.")

    nodes = [(acb(0, 1) * (2 * j * arb.pi() / SAMPLE_COUNT)).exp()
             for j in range(SAMPLE_COUNT)]
    readings = [(center + h * node).zeta() for node in nodes]
    coefficients = [
        sum((readings[j] * nodes[(-k * j) % SAMPLE_COUNT] for j in range(SAMPLE_COUNT)), acb(0))
        / SAMPLE_COUNT
        for k in range(DEGREE + 1)
    ]
    q = radius / outer
    alias = (h / outer) ** SAMPLE_COUNT
    error = (cauchy_bound / (1 - q)) * (q ** (DEGREE + 1) + alias / (1 - alias))
    if not (error < arb(1) / 10**9):
        raise ArithmeticError("The interpolation and truncation allowance is too large.")
    return h, coefficients, error.upper()


def evaluate(coefficients: list[acb], w: acb) -> acb:
    total = acb(0)
    for coeff in reversed(coefficients):
        total = total * w + coeff
    return total


def check() -> dict:
    ctx.prec = 144
    center = acb(arb(3) / 4, HEIGHT)
    radius = arb(31) / 128
    h, coefficients, error = zeta_polynomial(center, radius)
    uncertainty = acb(arb(0, error), arb(0, error))
    pi = arb.pi()
    log_pi = pi.log()
    slope = (arb(HEIGHT) / (2 * pi)).log() / 2
    scale = abs((-log_pi * center / 2).exp() * (center / 2).gamma())
    if not scale > 0:
        raise ArithmeticError("The normalization is not enclosed away from zero.")

    imaginary_unit = acb(0, 1)
    turns = (acb(1), imaginary_unit, acb(-1), -imaginary_unit)
    axis = acb(15, 8) / 17
    margin = arb(1) / 16
    pending = [(k, 4, j) for k in range(4) for j in range(15, -1, -1)]
    tested = 0
    accepted = []
    least_lower = None
    while pending:
        quarter, depth, index = pending.pop()
        n = 2**depth
        t = arb(2 * index + 1) / (2 * n) + arb(0, arb(1) / (2 * n))
        rational_arc = (1 + imaginary_unit * t) / (1 - imaginary_unit * t)
        offset = radius * turns[quarter] * rational_arc
        w = center + offset
        zeta = evaluate(coefficients, offset / h) + uncertainty
        gamma = (-log_pi * w / 2 - slope * offset).exp() * (w / 2).gamma()
        signed = -(axis * gamma * zeta / scale).imag
        tested += 1
        if signed > margin:
            lower = signed.lower()
            least_lower = lower if least_lower is None else min(least_lower, lower)
            accepted.append((quarter, depth, index))
        elif depth < 13:
            pending.extend(((quarter, depth + 1, 2 * index + 1), (quarter, depth + 1, 2 * index)))
        else:
            raise ArithmeticError(
                f"Unresolved quarter {quarter}, parameter cell {index}/{n}, enclosure {signed}."
            )

    # Each closed uniform cell lies in one of the accepted closed intervals.
    max_depth = max(depth for _, depth, _ in accepted)
    cells_per_quarter = 2**max_depth
    coverage = [[0] * cells_per_quarter for _ in turns]
    for quarter, depth, index in accepted:
        width = 2 ** (max_depth - depth)
        for cell in range(index * width, (index + 1) * width):
            coverage[quarter][cell] += 1
    if any(count != 1 for quarter in coverage for count in quarter):
        raise ArithmeticError("The accepted intervals did not partition the uniform mesh.")

    return {
        "pythonFlint": flint.__version__,
        "flint": flint.__FLINT_VERSION__,
        "precisionBits": ctx.prec,
        "center": [0.75, HEIGHT],
        "radius": "31/128",
        "zetaPointEvaluations": SAMPLE_COUNT,
        "polynomialDegree": DEGREE,
        "cauchyRadius": "1/2",
        "FourierRadius": "5/16",
        "uniformZetaErrorUpper": error.str(14),
        "testedCells": tested,
        "acceptedClosedCells": len(accepted),
        "maximumSubdivisionDepth": max_depth,
        "uniformCellsPerQuarter": cells_per_quarter,
        "coveredUniformCells": len(turns) * cells_per_quarter,
        "lowestSignedLowerBound": least_lower.str(12),
        "wholeBoundaryNormalizedMarginGreaterThan": "1/16",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
