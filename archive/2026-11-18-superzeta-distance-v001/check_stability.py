"""Check exact rational radius and error thresholds for the Rouché corollary."""
from fractions import Fraction as Q
import json
from pathlib import Path
import sys


def check(folder):
    radius, tolerance = Q(1,1000), Q(3,1000)
    for k in (2,3):
        record = json.loads((folder/f"distance-h{k}.json").read_bytes())
        assert record["harmonic"] == k
        assert Q(record["distance_coefficient_s"]) * radius > tolerance
        assert Q(1,4) > radius  # distance from a line zero to either vertical edge, in s
        for cell in record["cells"]:
            lo, hi = map(Q,cell["height_offset_cell"])
            a, b = map(Q,cell["root_height_offset_bracket"])
            assert min(a-lo,hi-b)/2 > radius
        print(f"H{k}: all s-disks of radius {radius} lie strictly inside their own cells;"
              f" uniform error at most {tolerance} preserves exactly one zero per disk.")


if __name__ == "__main__":
    check(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent)
