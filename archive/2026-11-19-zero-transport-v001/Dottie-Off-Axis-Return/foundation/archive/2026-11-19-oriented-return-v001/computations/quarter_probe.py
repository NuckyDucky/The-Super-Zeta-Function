"""Reconstruct the centerline witness from a calibrated pair of squared spectra.

Computes the period, branch slope and angle range before using the two
reciprocal-root readings. The decoder accepts only its two real measurements.
Run from a checkout with Python 3.12 and python-flint 0.9.0.
"""
from fractions import Fraction
import json

from flint import acb, arb, arb_series, ctx

from orbit_crossing import BRANCH_START, BRANCH_END, SLOPE_MIN, advance, rational as real, stage, verify


def square_trace(unit):
    """First reciprocal-root sum via the normalized determinant's series."""
    u = arb_series([0, 1], 4)
    c, h = unit.real, -unit.imag
    assert not c.contains(0), "The normalized squared determinant has c=0"
    left = c * u.cos() + h * u.sin()
    right = c * u.cos() - h * u.sin()
    product = (u - left) * (-u - right) / (c*c)
    return -product.log()[2]


def encode(unit):
    forward = acb(arb(3).sqrt()/2, arb(1)/2)
    return square_trace(unit*forward), square_trace(unit*forward.conjugate())


def decode(readings):
    up, down = [1-2/m for m in readings]
    return acb(up-down, (up+down)/arb(3).sqrt())


def degree(unit):
    return unit.arg()*180/arb.pi()


def cap_disk(y):
    L = acb(0, y)
    disk = acb(1), real("1e-15")
    for _ in range(3):
        center, radius, _, _ = advance(*disk, L, 320)
        disk = center, radius
    return disk


def unit(y):
    L = acb(0, y)
    disk = cap_disk(y)
    total = acb(0)
    for _ in range(320):
        for rate in [-L, L]:
            center, radius = disk
            error = arb(0, radius)
            total += rate*(center+acb(error, error))
            disk = stage(*disk, rate)
    # (-L)*L is positive on this centerline; the imaginary part of the
    # sum therefore gives the lifted phase of the complete multiplier.
    return acb(0, total.imag).exp()


def select(theta, digits, phase_at):
    lo, hi = BRANCH_START, BRANCH_END
    assert degree(phase_at(real(lo))) < theta < degree(phase_at(real(hi)))
    tol = Fraction(1, 10**digits)
    while hi-lo > tol:
        mid = (lo+hi)/2
        trial = degree(phase_at(real(mid)))
        if trial < theta:
            lo = mid
        elif theta < trial:
            hi = mid
        else:
            assert abs(theta-trial) < real(tol/2)*real(SLOPE_MIN)
            lo, hi = max(lo, mid-tol/2), min(hi, mid+tol/2)
    return lo, hi


def ordered_history(y):
    """640 ordered input pairs (U,V). Centerline symmetry gives Q=conj(P)."""
    L = acb(0, y)
    center, radius = cap_disk(y)
    for _ in range(640):
        error = arb(0, radius)
        P = center + acb(error, error)
        yield L * P.conjugate(), -L * P
        center, radius = stage(center.conjugate(), radius, L)


def run():
    calibration = verify()
    phase_at = unit
    original = Fraction("0.509892982511772")
    def pack(bounds):
        return real(bounds[0]).union(real(bounds[1]))
    def report(readings, theta, bounds):
        return dict(trace_plus=readings[0].str(30), trace_minus=readings[1].str(30),
                    angle_deg=theta.str(28), y=pack(bounds).str(37),
                    rational_bounds=[str(endpoint) for endpoint in bounds])

    initial_unit = phase_at(real(original))
    start = encode(initial_unit)
    initial = degree(decode(start))
    direct = select(initial, 34, phase_at)
    assert direct[0] <= original <= direct[1]
    clockwise = acb(arb(3).sqrt()/2, -arb(1)/2)
    turned = select(degree(decode(start)*clockwise), 35, phase_at)
    # Fresh measurement at the enclosure found by the preceding search.
    reduced_readings = encode(phase_at(pack(turned)))
    restored_unit = decode(reduced_readings)*clockwise.conjugate()
    restored = select(degree(restored_unit), 29, phase_at)
    assert restored[0] <= original <= restored[1]

    assert start[0] > start[1] and initial > -90
    assert reduced_readings[0] < reduced_readings[1] and degree(decode(reduced_readings)) < -90
    assert restored[1] - restored[0] < Fraction(1, 10**29)

    # Replay the rooted orbit once at the decoded parameter enclosure.
    # Inclusion of y0 and uniqueness on the branch identify the orbit.
    # Overlap of its lifted stages is a separate finite cross-check.
    gap = arb(0)
    stages_checked = 0
    for at_source, at_return in zip(ordered_history(real(original)),
                                     ordered_history(pack(restored)), strict=True):
        for src, ret in zip(at_source, at_return, strict=True):
            assert src.overlaps(ret)
            gap = max(gap, abs(src - ret).upper())
        stages_checked += 1
    assert stages_checked == 640
    assert gap < real("2.092e-20")
    mirror = -initial_unit.conjugate()
    for actual_angle, mirrored_angle in [(initial_unit, mirror),
                                          (initial_unit.conjugate(), mirror.conjugate())]:
        assert (square_trace(actual_angle)-square_trace(mirrored_angle)).contains(0)
    assert not encode(mirror)[0].overlaps(start[0])
    ninety = encode(acb(0, -1))
    exact = 8-4*arb(3).sqrt()
    assert all((m-exact).contains(0) for m in ninety)
    assert decode(ninety).real.contains(0)
    return dict(precision_bits=ctx.prec, witness_y=str(original),
                scalar_period=calibration["scalar_period"], ordered_period=calibration["ordered_period"],
                ordered_lift_pairs_compared=stages_checked,
                all_ordered_lift_boxes_overlap=True,
                max_lift_difference_upper=gap.str(14),
                original=report(start, initial, direct),
                clockwise=report(reduced_readings, degree(decode(reduced_readings)), turned),
                restored_y=pack(restored).str(36),
                restored_rational_bounds=[str(endpoint) for endpoint in restored],
                restored_width_upper="1e-29",
                original_contained_in_restored_bounds=True,
                unshifted_trace_boxes_overlap_at_reflection_for_both_stage_orders=True,
                positive_probe_boxes_disjoint_at_reflection=True,
                pivot_traces_enclosing_exact_tie=[m.str(25) for m in ninety])


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
