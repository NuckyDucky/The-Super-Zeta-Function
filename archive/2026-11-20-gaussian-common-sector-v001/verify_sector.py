"""Enclose the angular spread of all 193 completed Gaussian sums at each input."""
import gzip
import json
import sys
from pathlib import Path

from flint import arb

BLOCKS = Path(__file__).resolve().parent.parent / "2026-11-20-gaussian-relative-remainder-v001"
sys.path.insert(0, str(BLOCKS))
from verify import PHASES, completed, phase

LIMIT = arb(292) / 100


def covers_arc(models, lo, hi, depth=0):
    theta = lo.union(hi)
    anchor = models[0](theta)
    bottom, top = arb(0), arb(0)
    if abs(anchor) > 0:
        for model in models[1:]:
            ratio = model(theta) / anchor
            if not abs(ratio) > 0:
                break
            angle = ratio.arg()
            if not angle.is_finite():
                break
            bottom = min(bottom, angle.lower())
            top = max(top, angle.upper())
            if not top - bottom < LIMIT:
                break
        else:
            return 1
    if depth >= 16:
        raise ArithmeticError(f"Unresolved common sector on [{lo}, {hi}]")
    mid = (lo + hi) / 2
    return covers_arc(models, lo, mid, depth + 1) + covers_arc(models, mid, hi, depth + 1)


def load_models():
    with gzip.open(PHASES / "moments.json.gz", "rt") as stream:
        records = json.load(stream)["cutoffs"]
    cutoffs = list(range(2**26, 2**28 + 1, 2**20))
    if sorted(map(int, records)) != cutoffs:
        raise ValueError("Unexpected norm cutoffs")
    return cutoffs, [completed(n, records[str(n)]) for n in cutoffs]


def main():
    cutoffs, models = load_models()
    grid = [phase.TAU * j / 256 for j in range(257)]
    leaves = sum(covers_arc(models, lo, hi) for lo, hi in zip(grid, grid[1:]))

    # This pair bounds the worst-case spread from below. Its phase difference
    # is already less than pi by the uniform sector proof.
    sample = phase.TAU * 537 / 1024
    first = models[cutoffs.index(111149056)](sample)
    last = models[cutoffs.index(203423744)](sample)
    separation = abs((last / first).arg())
    if not arb(290) / 100 < separation < LIMIT:
        raise ArithmeticError("Lower bound on the maximum spread did not reproduce")
    if not (LIMIT < arb.pi() and (LIMIT / 2).cos() > arb(11) / 100):
        raise ArithmeticError("Lower projection bound did not reproduce")
    print(f"{len(models)} cutoffs covered on {leaves} complete arcs")
    print("Maximum angular spread on the right circle: 2.90 < width < 2.92 radians")
    print("Measured separation at 537*pi/512:", separation)


if __name__ == "__main__":
    main()
