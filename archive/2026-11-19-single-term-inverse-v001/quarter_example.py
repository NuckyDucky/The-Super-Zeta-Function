"""Exact Bernoulli fold and its three continued Dottie cycles. Python 3.12, python-flint 0.9.0.

Usage: python -B quarter_example.py PATH_TO_SUPER_ZETA_GIT_CHECKOUT
"""
import argparse
import json
from pathlib import Path
import sys

from flint import acb, acb_series, arb, ctx, fmpq, fmpq_poly


def exact_polynomials():
    x = fmpq_poly([0, 1])
    b2 = x*x - x + fmpq(1, 6)
    b3 = x**3 - fmpq(3, 2)*x*x + x/2
    a = -b3/3
    assert a.derivative() == -b2
    assert a + a(1-x) == 0
    assert a(fmpq(1, 5)) == fmpq(-2, 125)
    assert b3 - fmpq(6, 125) == (x-fmpq(1,5))*(x*x-fmpq(13,10)*x+fmpq(6,25))
    k = 2*x
    delta = k*(k-1)*(k-2)/12
    assert delta == -2*a
    return {"H_minus2_identically_zero": True, "marked_term": "-B3(b)/3",
            "order_contrast_equals_minus_twice_term": True,
            "shared_reading": "-2/125", "factorization_verified_over_Q": True}


def run(repo):
    ctx.prec, ctx.cap = 448, 5
    algebra = exact_polynomials()
    archive = repo.resolve() / "archive"
    sys.path[:0] = [str(archive/"2026-11-19-oriented-return-v001"/"computations"),
                    str(archive/"2026-11-19-zero-transport-v001"/"Dottie-Off-Axis-Return")]
    import flank_path as f
    from orbit_crossing import advance, stage
    from quarter_probe import degree
    from verify_dottie_horn_slice import trapping_data
    f.advance, f.stage, f.degree, f.trapping_data = advance, stage, degree, trapping_data
    ctx.prec, ctx.cap = 448, 5
    lo, hi, chart = f.calibration(1)
    sqrt3 = arb(3).sqrt()
    shifts = [arb(1)/5, (1-1/sqrt3)/2, (13-arb(73).sqrt())/20]
    assert arb(1)/6 < shifts[0] < shifts[1] < shifts[2] < arb(1)/4

    rows = []
    for label, b in zip(("1/5", "(1-1/sqrt(3))/2", "(13-sqrt(73))/20"), shifts, strict=True):
        theta = 90 - 180*b
        left, right = f.tinybracket(1, theta, lo, hi)
        state = f.moment(1, left, right, True)
        assert f.moment(1, left, left, False)["a"] < theta < f.moment(1, right, right, False)["a"]
        mu = abs(state["mu"])
        assert mu > 0 and mu < 1 and state["slope"] > 0 and state["k"] < 1
        w = acb_series([acb(-2), 1], 2)
        h = w.zeta(b) + w.zeta(1-b)
        marked = acb(-2).zeta(b)
        assert h[0].contains(0) and not h[1].contains(0)
        if label in ("1/5", "(13-sqrt(73))/20"):
            assert marked.contains(-arb(2)/125)
        else:
            assert (b*b-b+arb(1)/6).contains(0)
            assert (1-2*b).overlaps(1/sqrt3)
            assert marked.overlaps(-1/(36*sqrt3))
        rows.append({"shift_exact": label, "shift":b.str(22), "clockwise_degrees":(60-theta).str(20),
                     "marked_term":marked.str(21), "H_w":h[1].str(20),
                     "ImL": f.real(left).union(f.real(right)).str(26),
                     "abs_multiplier":mu.str(23), "native_degrees_per_ImL":state["slope"].str(16)})
    return {"working_precision_bits":ctx.prec, "algebra":algebra, "right_flank_calibration":chart, "values":rows}


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled.")
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("repo", type=Path)
    p.add_argument("--output", type=Path, default=Path(__file__).with_name("quarter_example.json"))
    args = p.parse_args()
    receipt = run(args.repo)
    args.output.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    for row in receipt["values"]:
        print(row["shift_exact"], row["marked_term"], row["abs_multiplier"])
