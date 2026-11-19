"""Recompute the two maps and their certified witnesses in a fresh directory."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from flint import arb, ctx
import numpy as np
from PIL import Image

from replay_single_term import compare


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / "archive"
ATLAS = ARCHIVE / "2026-11-19-dottie-plane-atlas-v001" / "atlas"


def read(path):
    return json.loads(path.read_bytes())


def check_reference():
    ref = read(ATLAS / "plane_reference.json")
    track = ARCHIVE / "2026-11-19-zero-transport-v001" / ref["source_file"]
    folds = ARCHIVE / "2026-11-19-sixth-passes-v001" / "compute" / "jets.json"
    assert sha256(track.read_bytes()).hexdigest() == ref["source_sha256"]
    assert sha256(folds.read_bytes()).hexdigest() == ref["cutoff_source_sha256"]
    minimum = next(row["bounds"] for row in read(folds)["events"] if row["id"] == "minimum")
    assert all(value == minimum[key] for key, value in ref["trough"].items())
    points = {row["shift"]: row for row in read(track)["checkpoints"]}
    shifts = [Fraction(row["shift"]) for row in ref["checkpoints"]]
    assert len(shifts) > 1 and shifts == sorted(set(shifts)) and shifts[-1] == Fraction(1, 4)
    for row in ref["checkpoints"]:
        assert row == points[row["shift"]]


def run(script, out, *args):
    print(f"Recomputing {script.name}", flush=True)
    proc = subprocess.run([sys.executable, "-B", str(script), *map(str, args)],
                          cwd=out, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.returncode:
        raise RuntimeError(proc.stdout.decode("utf-8", errors="replace"))


def compare_map(out):
    report = read(out / "plane_map.json")
    assert report["accepted"] + report["unresolved"] == report["grid_count"] == 10961
    assert report["max_common_node_disagreement"] <= report["agreement_threshold"]
    assert report["max_relative_level_drift"] <= report["level_drift_threshold"]
    with np.load(ATLAS / "plane_map.npz", allow_pickle=False) as old, \
         np.load(out / "plane_map.npz", allow_pickle=False) as new:
        for field in ("x", "y", "accepted", "marked_h", "marked_w"):
            np.testing.assert_array_equal(new[field], old[field])
        valid = old["accepted"]
        assert valid.sum() == report["accepted"]
        # These are floating-point trajectories. The interval anchors below
        # check contraction and expansion independently on two lifted levels.
        for field in ("end", "log2_length"):
            np.testing.assert_allclose(new[field][valid], old[field][valid], rtol=1e-7, atol=1e-6)
    return report


def replay(out):
    check_reference()
    run(ATLAS / "plane_map.py", out, "--output", out)
    for name in ("plane_strain.png", "plane_grid.png"):
        with Image.open(out / name) as regenerated, Image.open(ATLAS / name) as saved:
            assert regenerated.size == saved.size and min(regenerated.size) >= 1440
            regenerated.verify()
    report = compare_map(out)
    run(ATLAS / "plane_anchors.py", out, "--output", out)
    run(ATLAS / "phase_lift.py", out, "--repo", ROOT, "--out", out / "phase_lift.json")
    for name in ("plane_anchors.json", "phase_lift.json"):
        compare(read(out / name), read(ATLAS / name), name)
    lift = read(out / "phase_lift.json")
    assert lift["stages"] == 640 and lift["lifted_winding_relative_to_45_degrees"] == -1
    assert arb(lift["sixth_length_factor"]) < 1
    run(ATLAS / "basin_certificate.py", out, "--input", out / "phase_lift.json",
        "--output", out / "basin_certificate.json")
    cert = read(out / "basin_certificate.json")
    compare(cert, read(ATLAS / "basin_certificate.json"), "basin_certificate.json")
    for route in ("principal_k4", "ordered_rho6"):
        assert Fraction(cert[route]["initial_disk_radius"]) >= Fraction(1, 10**6)
        assert arb(cert[route]["uniform_tail_contraction"]) < 1
    shutil.copyfile(ATLAS / "critical_loop.py", out / "critical_loop.py")
    run(out / "critical_loop.py", out)
    loop = read(out / "critical_loop.json")
    compare(loop, read(ATLAS / "critical_loop.json"), "critical_loop.json")
    assert loop["winding"] == 1
    run(ATLAS / "critical_branches.py", out, "--input", out / "critical_loop.json",
        "--output", out / "critical_branches.json")
    branches = read(out / "critical_branches.json")
    compare(branches, read(ATLAS / "critical_branches.json"), "critical_branches.json")
    assert branches["square_root_signs"] == {"elementary_k4": -1, "riemann_6": 1}
    shutil.copyfile(ATLAS / "basin_map.py", out / "basin_map.py")
    run(out / "basin_map.py", out)
    with np.load(ATLAS / "basins.npz", allow_pickle=False) as old, \
         np.load(out / "basins.npz", allow_pickle=False) as new:
        classes = new["classes"]
        resolved = (classes[0] >= 0) & (classes[1] >= 0)
        changed = int((resolved & (classes[0] != classes[1])).sum())
        for field in ("xs", "ys", "raw", "classes"):
            np.testing.assert_array_equal(new[field], old[field])
    basin = read(out / "basin-summary.json")
    assert basin["probes"]["37j"] == ["Elementary k=4", "Riemann #6"]
    assert basin["different"] == changed and basin["both_resolved"] == int(resolved.sum())
    print(f"Reproduced {report['accepted']} accepted plane-map points and {basin['different']} changed destinations.", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions for directed checks.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New or empty folder for the generated maps.")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as fallback, ctx.workprec(768):
        output = args.output.resolve() if args.output else Path(fallback)
        output.mkdir(parents=True, exist_ok=True)
        if any(output.iterdir()):
            raise ValueError("Choose an empty output directory.")
        replay(output)
