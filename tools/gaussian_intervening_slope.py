"""Check the horizontal Gaussian derivative after consecutive signed norm blocks."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import gzip
import hashlib
import json
from math import factorial
from pathlib import Path
import sys

from flint import acb, arb, ctx

from gaussian_moments import ARCHIVE, BITS, FROZEN, LAST, ORDER, WIDTH, compute_block
from gaussian_prefix_smoothing import prefix_bounds

sys.path.insert(0, str(ARCHIVE / "2026-11-20-gaussian-circle-phases-v001"))
import replay as phase

REFERENCE = 276824064
BASELINE = 293601280
FINAL = BASELINE + 64 * WIDTH
EDGE_PARTS = 256
SAVED = Path(__file__).resolve().parents[1] / "archive/2026-11-21-gaussian-rectangle-v001/gaussian-intervening-slope.json"


def block_data(lo):
    lo, raw, nonzero, mass, sums = compute_block(lo)
    carrier_max = None
    line_changes = None
    if lo >= BASELINE:
        import numpy as np
        coeffs = np.frombuffer(raw, dtype="<i4")
        carrier, largest = acb(0), arb(0)
        heights = (-arb(35)/2048, arb(27)/2048)
        log_h = arb(lo).log()
        line_factors = [2*phase.arc.gamma(acb(0,y))*acb(0,-y*log_h).exp() for y in heights]
        upper_bottom, lower_top = arb(0), arb(0)
        for i in np.flatnonzero(coeffs):
            log_n = arb(lo+int(i)+1).log()
            carrier += int(coeffs[i]) * (-phase.s0*log_n).exp()
            largest = max(largest, abs(carrier).upper())
            upper_bottom = max(upper_bottom,(line_factors[0]*carrier).real.upper())
            lower_top = min(lower_top,(line_factors[1]*carrier).real.lower())
        ell = (arb(lo+WIDTH)/lo).log().upper()
        residuals = [abs(f)*largest*2*abs(y)*ell*(abs(y)*ell).exp()
                     for f,y in zip(line_factors,heights,strict=True)]
        carrier_max = str(largest)
        line_changes = str((upper_bottom+residuals[0]).upper()), str((lower_top-residuals[1]).lower())
    return lo, hashlib.sha256(raw).hexdigest(), nonzero, mass, sums, carrier_max, line_changes


def partial_block_bounds(lo, carrier, scale):
    # Abel summation transfers every ordered partial carrier at s0 to the
    # rectangle. The second bound includes differentiation of the gamma factor.
    rect = acb((arb(-63)/2048).union(arb(63)/2048),
               (arb(-35)/2048).union(arb(27)/2048))
    d = abs(rect).upper()
    L = (arb(lo+WIDTH)/lo).log().upper()
    log_h = arb(lo).log()
    g = abs(phase.arc.gamma0)*((rect*(phase.arc.logBt-log_h)).real.upper()
                               +3*d/(phase.arc.T-1)).exp()
    c = abs(phase.arc.B.log()+(phase.s0+rect).digamma()-log_h)
    e = (d*L).exp()
    u = carrier*(1+2*d*L*e)
    v = carrier*L*(2+d*L)*e
    return (2*g*u/scale).upper(), (2*g*(c*u+v)/scale).upper()


def rectangle_edges(parts):
    xm, half, mid = arb(63)/2048, arb(31)/2048, -arb(1)/512
    for j in range(parts):
        t = (arb(j)/parts).union(arb(j+1)/parts)
        yield acb(xm*t, mid-half)
        yield acb(xm*t, mid+half)
        yield acb(0, mid+half*(2*t-1))
        yield acb(xm, mid+half*(2*t-1))


def value(z):
    return phase.arc.partial(arb(1)/2+z.real, z.imag)


def negative_slope(z, scale):
    dz = phase.log_derivative_term(z)[1]
    reflected = phase.log_derivative_term(-z.conjugate())[1]
    return -(dz-reflected.conjugate()).imag/scale


def retained_terms(scale):
    directory = ARCHIVE / "2026-11-21-gaussian-rectangle-v001"
    sys.path.insert(0, str(directory))
    from retained import band_evaluator, far_tail_bound
    pad = arb(1)/8192
    band_rows = json.loads((directory/"carriers.json").read_text(encoding="utf-8"))
    assert len(band_rows) == 6
    bounds = sorted((r["lo"],r["hi"]) for r in band_rows)
    X, tail = far_tail_bound(phase.arc.T,phase.arc.B,pad)
    assert FINAL < bounds[0][0] and bounds[-1][1] <= X
    assert all(b[1] < c[0] for b,c in zip(bounds,bounds[1:]))
    bands = [band_evaluator(r,phase) for r in band_rows]
    rect = acb((-arb(63)/2048-pad).union(arb(63)/2048+pad),
               (-arb(35)/2048-pad).union(arb(27)/2048+pad))
    uniform = ((abs(sum(band(rect) for band in bands))+tail)/scale).upper()
    def bracket(cutoff):
        low_error, _ = prefix_bounds(cutoff,12)
        radius = ((tail+low_error)/scale).upper()
        def line(y):
            z = acb(0,y)
            return (value(z)+sum(band(z) for band in bands)).real/scale + arb(0,radius)
        lo, hi = -arb(35)/2048, arb(27)/2048
        for _ in range(40):
            middle = (lo+hi)/2
            f = line(middle)
            if f < 0:
                lo = middle
            elif f > 0:
                hi = middle
            else:
                break
        lo_sign, hi_sign = line(lo).upper(), line(hi).lower()
        assert lo_sign < 0 < hi_sign
        return {"offset_from_T_D":[str(lo),str(hi)], "bracket_real_sign_bounds":[str(lo_sign),str(hi_sign)]}
    return bracket, uniform, (uniform/pad).upper()


def classify(scale, edges):
    # The entire interval on each edge is enclosed. The extrema of Im f'
    # occur on those edges by harmonicity, then symmetry covers the other half.
    readings = [negative_slope(z, scale) for z in edges]
    lower = min(reading.lower() for reading in readings)
    upper = max(reading.upper() for reading in readings)
    ymin, ymax = -arb(35)/2048, arb(27)/2048
    def line(y):
        return value(acb(0, y)).real/scale
    fa, fb = line(ymin), line(ymax)
    row = {"negative_slope_lower": str(lower), "negative_slope_upper": str(upper),
           "bottom_value": str(fa), "top_value": str(fb)}
    if lower > 0 and fa < 0 < fb:
        for _ in range(32):
            y = (ymin+ymax)/2
            v = line(y)
            if v < 0:
                ymin = y
            elif v > 0:
                ymax = y
            else:
                break
        assert line(ymin) < 0 < line(ymax)
        row["root_offset_from_T_D"] = [str(ymin), str(ymax)]
        row["bracket_real_sign_bounds"] = [str(line(ymin).upper()), str(line(ymax).lower())]
    if lower <= 0:
        # A broad interval cannot establish a reversal. A negative point can.
        points = ((acb(0, -arb(1)/512), "middle of critical line"),
                  *((box.mid(), str(box.mid())) for box in edges))
        for z, label in points:
            reading = negative_slope(z, scale)
            if reading < 0:
                row["reversed_at"] = {"offset": label, "negative_slope": str(reading)}
                break
    return row


def calculate(workers):
    ctx.prec = BITS
    with gzip.open(FROZEN, "rt", encoding="utf-8") as stream:
        anchor = json.load(stream)["cutoffs"][str(LAST)]
    assert anchor["divided_by_factorial"] and len(anchor["moments"]) == ORDER+1
    mass = arb(anchor["mass"])
    moments = [acb(arb(re), arb(im)) for re, im in anchor["moments"]]
    edges = list(rectangle_edges(EDGE_PARTS))
    rows = []
    augmented_zeros = {}
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for lo, digest, nonzero, block_mass, sums, carrier, line_changes in pool.map(
                block_data, range(LAST, FINAL, WIDTH)):
            hi = lo+WIDTH
            mass += arb(block_mass)
            for k, (real, imag) in enumerate(sums):
                moments[k] += acb(arb(real), arb(imag))/factorial(k)
            phase.arc.N, phase.arc.order = hi, ORDER
            phase.arc.mass, phase.arc.coeff_taylor = mass, moments
            if hi == REFERENCE:
                scale = abs(value(acb(0,-arb(1)/512)))
                assert scale > 0
                augmented_bracket, added_abs, added_slope = retained_terms(scale)
            row = {"through_norm": hi, "signed_int32le_block_sha256": digest, "nonzero": nonzero}
            if hi >= BASELINE:
                row.update(classify(scale, edges))
            if hi in (BASELINE,FINAL):
                augmented_zeros[str(hi)] = augmented_bracket(hi)
            if lo >= BASELINE:
                dv, dd = partial_block_bounds(lo, arb(carrier), scale)
                previous = rows[-1]
                interval = {"carrier_modulus_upper": carrier,
                            "value_change_upper": str(dv), "derivative_change_upper": str(dd),
                            "negative_slope_lower": str((arb(previous["negative_slope_lower"])-dd).lower()),
                            "bottom_value_upper": str((arb(previous["bottom_value"])+arb(line_changes[0])/scale).upper()),
                            "top_value_lower": str((arb(previous["top_value"])+arb(line_changes[1])/scale).lower())}
                row["all_integer_cutoffs_in_block"] = interval
            rows.append(row)
            if (hi-LAST) % (8*WIDTH) == 0:
                print(f"Through norm {hi:,}/{FINAL:,}", file=sys.stderr, flush=True)
    raw_value, raw_deriv = prefix_bounds(FINAL, 12)
    value_error = (raw_value/scale).upper()
    slope_error = (raw_deriv/scale).upper()
    for row in rows:
        if row["through_norm"] <= BASELINE:
            continue
        block = row["all_integer_cutoffs_in_block"]
        assert arb(block["negative_slope_lower"])-slope_error > arb("144.3147")
        assert arb(block["bottom_value_upper"])+value_error < arb("-0.77914")
        assert arb(block["top_value_lower"])-value_error > arb("4.02807")
        assert arb(block["negative_slope_lower"])-slope_error-added_slope > arb("144.3068")
        assert arb(block["bottom_value_upper"])+value_error+added_abs < arb("-0.77914")
        assert arb(block["top_value_lower"])-value_error-added_abs > arb("4.02807")
        lo_value, hi_value = map(arb, row["bracket_real_sign_bounds"])
        assert lo_value+value_error < 0 < hi_value-value_error, row["through_norm"]
    return {"bits": BITS, "moment_anchor": LAST, "scale_cutoff": REFERENCE,
            "scale": str(scale), "previous_slope_cutoff": BASELINE,
            "smooth_value_error_over_scale": str(value_error),
            "smooth_slope_error_over_scale": str(slope_error),
            "six_bands_and_infinite_tail_value_upper":str(added_abs),
            "six_bands_and_infinite_tail_derivative_upper":str(added_slope),
            "smoothed_prefix_plus_six_bands_and_infinite_tail_zeros":augmented_zeros,
            "new_blocks": 64, "width": WIDTH, "edge_parts": EDGE_PARTS, "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if not __debug__ or args.workers < 1:
        parser.error("Use Python assertions and choose at least one worker")
    computed = calculate(args.workers)
    if computed != json.loads(SAVED.read_text(encoding="utf-8")):
        raise ArithmeticError("The rebuilt slope certificate differs from the saved record")
    print(f"Rebuilt {computed['new_blocks']} consecutive blocks through norm {FINAL:,}.")


if __name__ == "__main__":
    main()
