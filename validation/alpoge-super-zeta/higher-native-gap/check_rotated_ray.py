"""Directed Arb bounds for the one-pole rotation of the native Dottie gap."""

from flint import acb, arb, ctx


def ordinate_and_phase(q):
    ratio = q / q.sinh()
    p = q.cosh() * (1 - ratio**2).sqrt()
    return p, p + ratio.asin()


def check_pole_geometry(pi, slope):
    q1_lower, q1_upper = arb("1.58722"), arb("1.58723")
    q2_lower, q2_upper = arb("1.98299"), arb("1.98300")
    p1_lower, phase1_lower = ordinate_and_phase(q1_lower)
    p1_upper, phase1_upper = ordinate_and_phase(q1_upper)
    p2_lower, phase2_lower = ordinate_and_phase(q2_lower)
    _, phase2_upper = ordinate_and_phase(q2_upper)
    assert phase1_lower < 5 * pi / 6 < phase1_upper
    assert phase2_lower < 7 * pi / 6 < phase2_upper
    # Both p(q)/q and p(q) increase for q>0. The proof is in the note.
    first_slope_upper = p1_upper / q1_upper
    second_slope_lower = p2_lower / q2_lower
    assert first_slope_upper < slope < second_slope_lower
    first_angle_lower = (p1_lower / q1_lower).atan()
    first_angle_upper = first_slope_upper.atan()
    theta = slope.atan()
    second_angle_lower = second_slope_lower.atan()
    assert first_angle_lower > arb("0.86797")
    assert first_angle_upper < arb("0.86798")
    assert second_angle_lower > arb("0.99803")
    assert (p1_upper**2 + q1_upper**2).sqrt() < 3
    assert theta - first_angle_upper > arb(1) / 20
    assert pi / 2 - first_angle_upper > arb(7) / 10
    print("First pole q in (1.58722, 1.58723)")
    print("Second pole q in (1.98299, 1.98300)")
    print("First pole angle lower bound", first_angle_lower.str(17))
    print("First pole angle upper bound", first_angle_upper.str(17))
    print("Rotated ray angle", theta.str(17))
    print("Second pole angle lower bound", second_angle_lower.str(17))
    print("Checked first pole |x| < 3 and theta - delta > 1/20")
    print("Checked pi/2 - delta > 7/10")


def log_derivative_gap(x):
    b = (-x).exp()
    common = 1 + (1 + 4 * x**2) * b**2 + b**4
    offset = 2 * x * (b - b**3)
    common_prime = (8 * x - 2 - 8 * x**2) * b**2 - 4 * b**4
    offset_prime = 2 * (1 - x) * b - 2 * (1 - 3 * x) * b**3
    minus_determinant = common - offset
    plus_determinant = common + offset
    assert minus_determinant.abs_lower() > 0
    assert plus_determinant.abs_lower() > 0
    return (
        (common_prime - offset_prime) / minus_determinant
        - (common_prime + offset_prime) / plus_determinant
    )


def check_ray_bound(slope):
    # On each cell the rectangle encloses the image of the whole ray segment.
    # y^-sigma <= 1/y below 1, and <= 1 above 1, for 0 <= sigma <= 1.
    inv_step = 128
    step = arb(1) / inv_step
    half_step = step / 2
    total = arb(0)
    for index in range(inv_step // 8, 16 * inv_step):
        left = index * step
        y = arb(left + half_step, half_step)
        g = log_derivative_gap(acb(y, -slope * y))
        weight_upper = 1 / left if index < inv_step else arb(1)
        total += step * weight_upper * g.abs_upper()
    print("Medium rotated-ray integral upper bound", total.abs_upper().str(17))

    # The short and far parts use the elementary estimates in the note.
    small = arb(70) / 3
    large = arb(1)
    scale = arb(5) / 3
    residual = scale * (small + total + large)
    assert residual < 64
    print("Full rotated-ray residual constant upper bound", residual.abs_upper().str(17))
    print("Checked residual < 64 exp(-theta t) for 0 <= Re(w) <= 1")


def main():
    ctx.prec = 128
    ctx.threads = 1
    print("Arb precision", ctx.prec)
    pi = arb.pi()
    slope = arb(4) / 3
    check_pole_geometry(pi, slope)
    check_ray_bound(slope)


if __name__ == "__main__":
    main()
