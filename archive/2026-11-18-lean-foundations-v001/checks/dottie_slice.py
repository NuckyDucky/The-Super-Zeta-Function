"""Certify the cap orbit at three points on the manuscript's off-axis witness slice."""

from flint import acb, arb, ctx

ctx.prec = 384
HEIGHT = "0.509892982511772"
OFFSET = "4.749479070945369e-8"
PERIOD = 320
BLOCKS = 48
DISK_RADIUS = arb("1e-27").upper()


def stage(center, radius, rate):
    value = (rate * center).exp()
    midpoint = acb(value.real.mid(), value.imag.mid())
    rounding = abs(value - midpoint).upper()
    growth = abs(value) * (abs(rate) * radius).expm1()
    return midpoint, (rounding + growth).upper()


def advance(center, radius, parameter, steps, *, monitor=False, exclusions=(PERIOD // 2, PERIOD // 5)):
    derivative_bound = arb(1)
    divisor_disks = {}
    for step in range(1, steps + 1):
        for rate in (-parameter, parameter):
            center, radius = stage(center, radius, rate)
            if monitor:
                derivative_bound = (
                    derivative_bound * abs(rate) * (abs(center) + radius)
                ).upper()
        if monitor and step in exclusions:
            divisor_disks[step] = (center, radius)
    return center, radius, derivative_bound, divisor_disks


def maximal_proper_divisors(period):
    remaining = period
    prime = 2
    divisors = []
    while prime * prime <= remaining:
        if remaining % prime == 0:
            divisors.append(period // prime)
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        divisors.append(period // remaining)
    return tuple(divisors)


def trapping_data(parameter, cap=1, period=PERIOD):
    # The first half-step uses -parameter. Changing its sign checks the other phase.
    center, orbit_radius, _, _ = advance(acb(cap), arb(0), parameter, period * BLOCKS)
    assert orbit_radius < DISK_RADIUS, "the cap orbit must enter the trapping disk"

    image_center, image_radius, _, _ = advance(center, arb(0), parameter, period)
    residual = (abs(image_center - center) + image_radius).upper()
    _, _, derivative_bound, divisor_disks = advance(
        center, DISK_RADIUS, parameter, period, monitor=True, exclusions=maximal_proper_divisors(period)
    )
    assert derivative_bound < 1
    assert residual + derivative_bound * DISK_RADIUS < DISK_RADIUS
    for divisor_center, divisor_radius in divisor_disks.values():
        assert abs(divisor_center - center) > divisor_radius + DISK_RADIUS

    return center, orbit_radius, residual, derivative_bound


def certify(parameter):
    _, orbit_radius, residual, derivative_bound = trapping_data(parameter)
    return orbit_radius, residual, derivative_bound


if __name__ == "__main__":
    print("Slice Im L =", HEIGHT)
    for x in ("-" + OFFSET, "0", OFFSET):
        parameter = acb(arb(x), arb(HEIGHT))
        for phase, rate in (("P", parameter), ("Q", -parameter)):
            orbit_radius, residual, bound = certify(rate)
            print(
                f"Re L = {x}, phase {phase}:",
                "primitive scalar period", PERIOD,
                "cap enclosure radius <=", orbit_radius.str(7),
                "return residual <=", residual.str(7),
                "contraction <=", bound.str(12),
            )
