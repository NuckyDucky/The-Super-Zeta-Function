"""Check the exponential reference and winding on the ordinary Cayley disk."""

from pathlib import Path
import runpy

from flint import acb, arb, ctx


def polygon_vertex(value):
    scale = 10**10
    x = round(float(value.real.mid()) * scale)
    y = round(float(value.imag.mid()) * scale)
    return (x, y), acb(arb(x) / scale, arb(y) / scale)


def winding(vertices):
    count = 0
    for (x, y), (next_x, next_y) in zip(vertices, vertices[1:] + vertices[:1]):
        cross = x * next_y - next_x * y
        count += int(y <= 0 < next_y and cross > 0)
        count -= int(next_y <= 0 < y and cross < 0)
    return count


def main(precision=144):
    ctx.prec, ctx.threads = precision, 1
    replay = runpy.run_path(str(Path(__file__).with_name("check-completed-circle.py")))
    i = acb(0, 1)
    center = acb(arb(3) / 4, replay["HEIGHT"])
    radius, outer = arb(31) / 128, arb(1) / 4
    h, coefficients, _ = replay["zeta_polynomial"](center, radius)
    cauchy_radius, majorant = arb(1) / 2, arb(10)**9
    turns = (acb(1), i, acb(-1), -i)

    def sample_error(r):
        ratio = r / cauchy_radius
        alias = h / cauchy_radius
        tail = majorant * ratio ** len(coefficients) / (1 - ratio)
        fourier = majorant * alias ** replay["SAMPLE_COUNT"] / ((1 - alias) * (1 - r / h))
        return (tail + fourier).upper()

    def polynomial(offset):
        return replay["evaluate"](coefficients, offset / h)

    def arc(r, quarter, t):
        return r * quarter * (1 + i * t) / (1 - i * t)

    a = acb(arb("1.0806411422"), arb("-1.6313279993"))
    b = acb(arb("-0.5026423523"), arb("1.9451577269"))
    assert abs(a) > 0

    def relative_bound(r):
        error = sample_error(r)
        padding = acb(arb(0, error), arb(0, error))
        upper = arb(0)
        cells = 512
        for turn in turns:
            for j in range(cells):
                t = arb(2 * j + 1) / (2 * cells) + arb(0, arb(1) / (2 * cells))
                offset = arc(r, turn, t)
                reference = a * (b * offset).exp()
                upper = max(upper, abs((polynomial(offset) + padding) / reference - 1).upper())
        return upper

    outer_bound = relative_bound(outer)
    outer_error = sample_error(outer)
    constant_error = (abs(coefficients[0] - a) + outer_error) / abs(a)
    slope_error = (
        abs(coefficients[1] / h - b * coefficients[0]) + outer_error / outer + abs(b) * outer_error
    ) / abs(a)
    inner_bound = constant_error + radius * slope_error + (
        outer_bound + constant_error + outer * slope_error
    ) * (radius / outer) ** 2
    direct_bound = relative_bound(radius)
    outer_limit = arb("1.01631")
    inner_limit = arb(".8954")
    assert 1 < outer_bound < outer_limit
    assert inner_bound < arb(".954")
    assert direct_bound < inner_limit
    print("Outer relative error", outer_bound)
    print("Inner relative error from Schwarz", inner_bound.upper())
    print("Inner relative error from direct intervals", direct_bound)

    height_half_width = arb(1) / 4096
    clearance = outer - radius - height_half_width
    assert clearance > 0
    height_drift = ((1 + outer_bound) * height_half_width / clearance).upper()
    height_margin = (1 - direct_bound - height_drift).lower()
    assert height_margin > arb(".0396")
    print("Height band center", replay["HEIGHT"], "with half width 1/4096")
    print("Cauchy height drift allowance", height_drift)
    print("Signed margin on every circle in the band", height_margin)

    target_margin = arb(".0396")
    allowed_loss = 1 - inner_limit - target_margin
    calculated_shift = (outer - radius) * allowed_loss / (outer_limit + allowed_loss)
    exact_shift = arb(1625) / 3460192
    assert (calculated_shift - exact_shift).contains(0)
    assert exact_shift > height_half_width
    calculated_clearance = outer - radius - exact_shift
    assert calculated_clearance > 0
    centered_drift = (outer_bound * exact_shift / calculated_clearance).upper()
    calculated_margin = (1 - direct_bound - centered_drift).lower()
    assert calculated_margin > target_margin
    print("Required signed margin", target_margin)
    print("Calculated height half width 1625/3460192", exact_shift)
    print("Verified centered drift allowance", centered_drift)
    print("Signed margin throughout the calculated band", calculated_margin)

    modulus_bound = sum(
        (abs(coeff) * (radius / h) ** k for k, coeff in enumerate(coefficients)), arb(0)
    ) + sample_error(radius)
    slope_bound = sum(
        (abs(coeff) * k / h * (radius / h) ** (k - 1)
         for k, coeff in enumerate(coefficients[1:], 1)),
        arb(0),
    ) + outer_error / (outer - radius)
    log2 = arb(2).log()
    normalizer = (log2 * center).exp() - 1
    assert abs(normalizer) > 0
    factor_bound = (log2 * (center.real + radius)).exp()
    two_lap_slope = (
        log2 * factor_bound * modulus_bound + (factor_bound + 1) * slope_bound
    ) / abs(normalizer)

    for two_laps, cells, minimum, outer_slope in (
        (False, 64, "0.2230", slope_bound),
        (True, 128, "0.04594", two_lap_slope),
    ):
        vertices, centers, budgets = [], [], []
        for turn in turns:
            for j in range(cells):
                offset = arc(radius, turn, arb(j) / cells)
                weight = (((center + offset) * log2).exp() - 1) / normalizer if two_laps else acb(1)
                value = weight * polynomial(offset)
                vertex, exact_center = polygon_vertex(value)
                vertices.append(vertex)
                centers.append(exact_center)
                budgets.append(
                    (abs(value - exact_center) + abs(weight) * sample_error(radius)
                     + 2 * radius * outer_slope / cells).upper()
                )
        margins = [
            (abs(p) - max(budgets[j], abs(centers[(j + 1) % len(centers)] - p))).lower()
            for j, p in enumerate(centers)
        ]
        assert all(margin > arb(minimum) for margin in margins)
        assert winding(vertices) == 0
        print("With two-lap factor", two_laps, "vertices", len(vertices), "winding", 0,
              "minimum homotopy margin", min(margins))


if __name__ == "__main__":
    main()
