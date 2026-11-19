"""Recompute the certificates from a clean checkout in fresh output directories."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from flint import arb

from layout import HERE, ROOT


def run(directory, script, *args):
    print(f"Checking {script} {' '.join(str(a) for a in args[:1])}", flush=True)
    proc = subprocess.run(
        [sys.executable, "-B", str(HERE / script), *map(str, args)],
        cwd=directory, env={**os.environ, "SINGLE_TERM_OUTPUT": str(directory)},
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode:
        raise RuntimeError(proc.stdout)


def read(directory, name):
    return json.loads((directory / name).read_bytes())


def overlap(fresh, recorded):
    assert arb(fresh).overlaps(arb(recorded)), (fresh, recorded)


def check_readings(out):
    run(out, "one_term.py", "encode")
    for fresh, old in zip(read(out, "packets.json"), read(HERE, "packets.json"), strict=True):
        for key in ("real", "imag"):
            overlap(fresh[key], old[key])
    # Decode the exact published input, including its rounding uncertainty.
    shutil.copyfile(HERE / "packets.json", out / "packets.json")
    run(out, "one_term.py", "decode")
    run(out, "one_term.py", "score")
    run(out, "recover_orbit.py", "recover", "--repo", ROOT)
    # Generate the answer key separately from the original crossing and orbit.
    run(out, "scoring/orbit_packets.py", ROOT, "--outdir", out / "scoring")
    run(out, "recover_orbit.py", "score", "--repo", ROOT, "--truth", out / "scoring" / "truth.json")
    fresh = read(out, "recovered-orbits.json")["recovered"]
    old = read(HERE, "recovered-orbits.json")["recovered"]
    for row, other in zip(fresh, old, strict=True):
        overlap(row["abs_multiplier"], other["abs_multiplier"])
        overlap(row["ImL"]["interval"], other["ImL"]["interval"])


def check_chart(out):
    run(out, "chart.py", "--full")
    fresh = read(out, "chart.json")
    assert fresh["transverse_double_points"] == 1 and fresh["joint_coordinate_is_injective"]
    lower, upper = map(arb, fresh["speed_enclosure"])
    assert lower > arb("0.10438") and upper < arb("3.84948")
    assert arb(fresh["uniqueness_on_collision_hull_lipschitz_upper"]) < arb("0.524")
    for name, bound in read(HERE, "chart-crossing.json")["bounds"].items():
        overlap(read(out, "chart-crossing.json")["bounds"][name], bound)
    run(out, "recover_orbit.py", "collision", "--repo", ROOT)
    for fresh, old in zip(read(out, "collision-orbits.json")["recovered"],
                          read(HERE, "collision-orbits.json")["recovered"], strict=True):
        overlap(fresh["abs_multiplier"], old["abs_multiplier"])


def check_attraction(out):
    run(out, "recover_orbit.py", "sweep", "--repo", ROOT)
    fresh = read(out, "contraction-sweep.json")
    rate = fresh["d_log_abs_mu_per_clockwise_degree"]
    assert arb(rate["lower"]) > arb("-0.008614") and arb(rate["upper"]) < arb("-0.005387")
    for key in ("initial_abs_mu", "terminal_abs_mu", "relative_decrease"):
        overlap(fresh[key], read(HERE, "contraction-sweep.json")[key])
    run(out, "quarter_example.py", ROOT, "--output", out / "quarter_example.json")
    values = read(out, "quarter_example.json")["values"]
    for fresh, old in zip(values, read(HERE, "quarter_example.json")["values"], strict=True):
        overlap(fresh["marked_term"], old["marked_term"])
        overlap(fresh["abs_multiplier"], old["abs_multiplier"])


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    checks = {"readings": check_readings, "chart": check_chart, "attraction": check_attraction}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=checks)
    parser.add_argument("--output", type=Path, help="New or empty directory for the replay records.")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        base = args.output.resolve() if args.output else Path(temp)
        base.mkdir(parents=True, exist_ok=True)
        if any(base.iterdir()):
            raise ValueError("Choose an empty output directory.")
        for key in ([args.part] if args.part else checks):
            out = base / key
            out.mkdir()
            checks[key](out)
            print(f"Passed {key}", flush=True)
