"""Replay this addendum from a fresh checkout. All archive inputs are read-only."""
import hashlib
import json
import os
from fractions import Fraction
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent
MATCH = ARCHIVE / "2026-11-17-dottie-grid-match-v001"
RETURNS = ARCHIVE / "2026-11-17-quartet-return-recursion-v001" / "computations"
OFFCENTER = ARCHIVE / "2026-11-17-offcenter-superzeta-v001"
DEPS = [MATCH, RETURNS, OFFCENTER]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    sys.path[:0] = [str(path) for path in DEPS]
    from dottie_grid_trial import centers, certify, ctx

    nomination = MATCH / "dottie-grid-nomination.json"
    forecast = MATCH / "dottie-grid-forecast.json"
    cert = json.loads((MATCH / "dottie-grid-certificate.json").read_bytes())
    prediction = json.loads(forecast.read_bytes())
    assert cert["nomination_sha256"] == prediction["nomination_sha256"] == digest(nomination)
    assert cert["forecast_sha256"] == digest(forecast)
    box = prediction["arms"]["dottie"]["broad"]
    left, right = map(Fraction, box["beta"])
    assert left < Fraction(1, 8) < Fraction(7, 8) < right
    assert tuple(map(Fraction, box["height_offset"])) == (Fraction(-1, 4), Fraction(1, 4))
    ctx.prec = 192
    _, height, _, _ = centers()
    actual = certify(height, prediction["arms"]["dottie"])
    assert actual == cert["arms"]["dottie"]
    broad = actual["broad"]
    assert broad["status"] == "certified" and broad["count"] == 2
    assert broad["off_line_upper_bound"] == 0
    (a, b), (c, d) = [tuple(map(Fraction, pair)) for pair in broad["line_brackets"]]
    assert Fraction(-1, 4) < a < b < 0 < c < d < Fraction(1, 4)
    print("Dottie arm agrees with the full archived numerical record.", flush=True)
    print("Broad count 2; two disjoint line brackets; off-line upper bound 0.", flush=True)
    print("Full allowed real interval [1/8,7/8] lies strictly inside the counted rectangle.", flush=True)

    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join([*map(str, DEPS), env.get("PYTHONPATH", "")]).rstrip(os.pathsep)
    for args in (["verify_dottie_half_gap.py", "--two-thirds"], ["verify_quartet_two_thirds_translation.py"]):
        subprocess.run([sys.executable, "-B", str(HERE / args[0]), *args[1:]], env=env, check=True)


if __name__ == "__main__":
    main()
