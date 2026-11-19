"""Replay the archived single-term proof and check its recorded enclosure precision."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
import tempfile

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "archive" / "2026-11-19-single-term-inverse-v001"
sys.path.insert(0, str(SNAPSHOT))
import replay as inverse


# The archive contains 192-, 224- and 448-bit calculations. Keep extra
# precision here when converting their printed decimal intervals back to Arb.
COMPARISON_PRECISION = 768
# Allow a 25% change in radius for backend and formatting differences.
RADIUS_RATIO = Fraction(5, 4)
RECORDS = {
    "readings": ("decoded.json", "recovered-orbits.json", "scoring/truth.json"),
    "chart": ("chart.json", "chart-crossing.json", "imaginary-axis.json", "collision-orbits.json"),
    "attraction": ("contraction-sweep.json", "quarter_example.json"),
}


def check_ball(fresh, saved, field):
    with ctx.workprec(COMPARISON_PRECISION):
        actual, baseline = arb(fresh), arb(saved)
        if not (actual.is_finite() and baseline.is_finite() and actual.overlaps(baseline)):
            raise ValueError(f"Disjoint or nonfinite enclosures at {field}")
        if actual.rad() * RADIUS_RATIO.denominator > baseline.rad() * RADIUS_RATIO.numerator:
            raise ValueError(f"Replay enclosure exceeds the archived radius budget at {field}")


def components(text):
    """FLINT's older answer key prints a complex box as two signed real balls."""
    pair = re.fullmatch(r"(\[[^\]]+\]) ([+-]) (\[[^\]]+\])j", text)
    if pair is None:
        return (arb(text),)
    real, sign, imag = pair.groups()
    return arb(real), arb(imag) if sign == "+" else -arb(imag)


def check_physical_interval(fresh, saved, field):
    bounds = []
    for entry in (fresh, saved):
        lo, hi = Fraction(entry["lower"]), Fraction(entry["upper"])
        if hi < lo or hi - lo != Fraction(entry["width"]):
            raise ValueError(f"Inconsistent exact rational endpoints at {field}")
        bounds.append((lo, hi))
    (a, b), (c, d) = bounds
    if b < c or d < a or b - a > RADIUS_RATIO * (d - c):
        raise ValueError(f"Exact parameter enclosure differs at {field}")


def compare(fresh, saved, field):
    if isinstance(saved, dict):
        if field.endswith("/ImL") and "lower" in saved:
            check_physical_interval(fresh, saved, field)
        return sum(compare(fresh[key], value, f"{field}/{key}") for key, value in saved.items())
    if isinstance(saved, list):
        return sum(compare(a, b, f"{field}/{i}")
                   for i, (a, b) in enumerate(zip(fresh, saved, strict=True)))
    if isinstance(saved, str) and saved.startswith("[") and "+/-" in saved:
        with ctx.workprec(COMPARISON_PRECISION):
            values = list(zip(components(fresh), components(saved), strict=True))
            for current, recorded in values:
                check_ball(current, recorded, field)
        return len(values)
    return 0


def self_test():
    # Both failures would pass a lower-precision or overlap-only comparison.
    for example, baseline in (("1.0000000000000000001", "1"),
                              ("1 +/- 1e-19", "1 +/- 1e-30")):
        try:
            check_ball(example, baseline, "self-test")
        except ValueError:
            continue
        raise ValueError(f"Comparison accepted the invalid example {example}")
    check_ball("1 +/- 2e-30", "1 +/- 2e-30", "self-test")


def check_part(part, directory):
    getattr(inverse, f"check_{part}")(directory)
    files = [(directory / name, SNAPSHOT / name) for name in RECORDS[part]]
    if part == "readings":
        # The archived decoder intentionally uses the frozen packets; regenerate
        # the encoder separately so the comparison also checks the original input.
        enc = directory / "encoding"
        enc.mkdir()
        inverse.run(enc, "one_term.py", "encode")
        files.append((enc / "packets.json", SNAPSHOT / "packets.json"))
    count = sum(compare(json.loads(a.read_bytes()), json.loads(b.read_bytes()), b.name)
                for a, b in files)
    print(f"{part}: verified {count} interval fields at {COMPARISON_PRECISION} bits.", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions for the archived proofs.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=RECORDS)
    parser.add_argument("--output", type=Path, help="New or empty directory for fresh records.")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as fallback, ctx.workprec(COMPARISON_PRECISION):
        self_test()
        output = args.output.resolve() if args.output else Path(fallback)
        output.mkdir(parents=True, exist_ok=True)
        if any(output.iterdir()):
            raise ValueError("Choose an empty output directory.")
        for part in ([args.part] if args.part else RECORDS):
            directory = output / part
            directory.mkdir()
            check_part(part, directory)
