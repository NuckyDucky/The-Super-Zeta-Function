"""Enclose the odd part and the horizontal derivative of completed Gaussian prefixes."""

import hashlib
import json
import sys
from pathlib import Path

from flint import acb, arb, ctx


HERE = Path(__file__).resolve().parent
INITIAL = 276824064
LAST = 293601280
STEP = 2**20


def rectangle_edges(xmax, mid_y, half_height, parts):
    for j in range(parts):
        t = (arb(j) / parts).union(arb(j + 1) / parts)
        yield acb(xmax * t, mid_y - half_height)
        yield acb(xmax * t, mid_y + half_height)
        yield acb(0, mid_y + half_height * (2 * t - 1))
        yield acb(xmax, mid_y + half_height * (2 * t - 1))


def check(repo):
    # The archive's verify.py has the same basename as this script.
    sys.path.insert(0, str(repo / "archive/2026-11-20-gaussian-relative-remainder-v001"))
    from verify import completed, phase

    ctx.prec = 256
    path = HERE / "signed-blocks.json"
    records = json.loads(path.read_text(encoding="utf-8"))["cutoffs"]
    xm, half_height, mid_y = arb(63) / 2048, arb(31) / 2048, -arb(1) / 512
    def install(cutoff):
        completed(cutoff, records[str(cutoff)])(arb(0))

    install(INITIAL)
    def value(z):
        return phase.arc.partial(arb(1) / 2 + z.real, z.imag)

    scale = abs(value(acb(0, mid_y)))
    assert scale > 0
    def derivative(z):
        left = phase.log_derivative_term(z)[1]
        right = phase.log_derivative_term(-z.conjugate())[1]
        return (left - right.conjugate()) / scale

    def real_on_line(height):
        reading = value(acb(0, height)) / scale
        assert reading.imag.contains(0)
        return reading.real

    def root_bracket(line_value):
        lo, hi = mid_y - half_height, mid_y + half_height
        lower_value, upper_value = line_value(lo), line_value(hi)
        assert lower_value < 0 < upper_value
        for _ in range(36):
            m = (lo + hi) / 2
            v = line_value(m)
            if v < 0:
                lo = m
            elif v > 0:
                hi = m
            else:
                break
        assert line_value(lo) < 0 < line_value(hi)
        return {"height_offset_bracket": [str(lo), str(hi)],
                "endpoint_signs": [str(lower_value), str(upper_value)]}

    small_grid = list(rectangle_edges(xm, mid_y, half_height, 128))
    endpoint_checks = []
    for j in range(INITIAL, LAST + 1, STEP):
        install(j)
        infimum_bound = min((-derivative(z).imag).lower() for z in small_grid)
        assert infimum_bound > 175
        endpoint_checks.append({"cutoff": j, "negative_imaginary_derivative_lower": str(infimum_bound),
                                **root_bracket(real_on_line)})

    # For the last cutoff refine both the half rectangle and the two-disk test.
    edge_parts = 2048
    derivative_bound = min((-derivative(z).imag).lower()
                           for z in rectangle_edges(xm, mid_y, half_height, edge_parts))
    assert derivative_bound > arb("194.01")
    arcs = 16384
    center_x = arb(1) / 64
    grid = [2 * arb.pi() * k / arcs for k in range(arcs + 1)]
    def disk_quotient(t):
        x = center_x + half_height * t.cos()
        y = mid_y + half_height * t.sin()
        assert x > 0
        return -value(acb(x, y)).imag / (x * scale)
    slope_lower = min(disk_quotient(a.union(b)).lower() for a, b in zip(grid, grid[1:]))
    slope_sample = min(disk_quotient(t).upper() for t in grid[::16])
    assert slope_lower > arb("205.93") and slope_sample < arb("206.15")

    # Positive control: multiply the prefix by 1−((w−c)/b)^2, b=1/64.
    # Its two forced zeros are the disk centers. At the right root the
    # normalized correction is −F_j/S0 and its derivative is
    # −2 F_j/(b S0) − F'_j/S0, with every sign independently testable.
    root = acb(center_x, mid_y)
    control_slope = -value(root).imag / (scale * center_x)
    control_derivative = (-2 * value(root) / (center_x * scale) - derivative(root)).imag
    assert control_slope > slope_lower and control_derivative > derivative_bound

    # Add six signed distant bands and the entire far tail in the SAME lambda=1
    # smoothing. The tail bound is archived for the widened whole rectangle;
    # a circle of radius pad around each point therefore fits its domain.
    from retained import band_evaluator, far_tail_bound
    carriers_path = HERE / "carriers.json"
    carrier_rows = json.loads(carriers_path.read_text())
    assert len(carrier_rows) == 6
    bands = [band_evaluator(v, phase) for v in carrier_rows]
    pad = arb(1) / 8192
    padded_rectangle = acb((-xm - pad).union(xm + pad),
                           (mid_y - half_height - pad).union(mid_y + half_height + pad))
    tail_cutoff, raw_tail = far_tail_bound(phase.arc.T, phase.arc.B, pad)
    far_tail = raw_tail / scale
    perturbation = (abs(sum(b(padded_rectangle) for b in bands)) / scale + far_tail).upper()
    cauchy = (perturbation / pad).upper()
    assert perturbation < arb("0.000000966") and cauchy < arb("0.00791")
    augmented_derivative_bound = derivative_bound - cauchy
    # Both the perturbation and prefix obey reflection. The imaginary part is
    # zero on the line, so the very same derivative cap bounds its slope
    # divided by x throughout the rectangle (also at small positive x).
    augmented_disk_bound = slope_lower - cauchy
    assert augmented_derivative_bound > 194 and augmented_disk_bound > arb("205.93")
    def augmented_line_value(y):
        six = sum(b(acb(0, y)) for b in bands).real / scale
        return real_on_line(y) + six + arb(0, far_tail.upper())
    augmented = {
        "lambda": 1, "sharp_prefix": LAST,
        "included_distant_bands": [[v["lo"], v["hi"]] for v in carrier_rows],
        "included_all_norms_strictly_above": tail_cutoff,
        "carriers_sha256": hashlib.sha256(carriers_path.read_bytes()).hexdigest(),
        "sup_perturbation_over_scale_padded_rectangle": str(perturbation),
        "sup_perturbation_derivative_over_scale_rectangle": str(cauchy),
        "negative_imaginary_derivative_lower": str(augmented_derivative_bound.lower()),
        "negative_imaginary_quotient_lower_right_disk": str(augmented_disk_bound.lower()),
        **root_bracket(augmented_line_value)}

    return {
        "input_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "bits": ctx.prec, "reference_cutoff": INITIAL, "reference_scale": str(scale),
        "tested_cutoff": LAST, "height_offsets_relative_to": "T_D",
        "rectangle_x": "[-63/2048,63/2048]",
        "rectangle_y": "[-35/2048,27/2048]", "coarse_edge_parts": 128,
        "edge_parts_per_side_of_half_rectangle": edge_parts,
        "negative_imaginary_derivative_lower": str(derivative_bound),
        "right_circumference_arcs": arcs,
        "negative_imaginary_slope_infimum": [str(slope_lower), str(slope_sample)],
        "occupied_polynomial_control_at_right_center": {
            "positive_remainder_imaginary_slope": str(control_slope),
            "positive_remainder_imaginary_derivative": str(control_derivative)},
        "prefix_boxes": endpoint_checks, "augmented_infinite_model": augmented}


if __name__ == "__main__":
    if not __debug__:
        sys.exit("Run with assertions enabled.")
    result = check(HERE.parents[1])
    known = json.loads((HERE / "certificate.json").read_text())
    for name in ("input_sha256", "tested_cutoff", "reference_cutoff", "rectangle_x", "rectangle_y"):
        assert result[name] == known[name]
    row = result["augmented_infinite_model"]
    assert row["carriers_sha256"] == known["augmented_infinite_model"]["carriers_sha256"]
    assert row["included_distant_bands"] == known["augmented_infinite_model"]["included_distant_bands"]
    assert row["included_all_norms_strictly_above"] == known["augmented_infinite_model"]["included_all_norms_strictly_above"]
    assert arb(row["negative_imaginary_derivative_lower"]) > arb("194.00274")
    assert arb(row["negative_imaginary_quotient_lower_right_disk"]) > arb("205.93192")
    lo, hi = map(arb, row["height_offset_bracket"])
    assert arb("-0.011443479006616") < lo < hi < arb("-0.011443479006175")
    print("All 17 prefix slopes and simple zeros checked.")
    print("Augmented function: -Im H'/S0 > 194.00274, height offset", lo.str(17), hi.str(17))
