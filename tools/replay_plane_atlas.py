"""Recompute the maps and interval proofs for the marked starting points and inverse branches."""
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


def compare_map(out, stem, expected_count):
    report = read(out / f"{stem}.json")
    assert report["accepted"] + report["unresolved"] == report["grid_count"] == expected_count
    assert report["max_common_node_disagreement"] <= report["agreement_threshold"]
    assert report["max_relative_level_drift"] <= report["level_drift_threshold"]
    with np.load(ATLAS / f"{stem}.npz", allow_pickle=False) as old, \
         np.load(out / f"{stem}.npz", allow_pickle=False) as new:
        fields = ["x", "y", "accepted"]
        if stem == "plane_map":
            fields.extend(("marked_h", "marked_w"))
        for field in fields:
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
    record = ARCHIVE / "2026-11-19-oriented-return-v001" / "data" / "quarter_probe.json"
    assert sha256(record.read_bytes()).hexdigest() == "7d3afc4ded30439ec277ef5a3636f187f1ae89ef8de5992ed77392068c1d051f"
    run(ATLAS / "two_paths.py", out, "--output", out)
    run(ATLAS / "trace_order.py", out, "--data", record, "--output", out / "trace_order.png")
    run(ATLAS / "plane_map.py", out, "--output", out)
    run(ATLAS / "plane_wide.py", out, "--output", out)
    for name in ("plane_strain.png", "plane_grid.png", "plane_wide.png", "trace_order.png", "two_paths.png"):
        with Image.open(out / name) as regenerated, Image.open(ATLAS / name) as saved:
            assert regenerated.size == saved.size and min(regenerated.size) >= 1440
            regenerated.verify()
    report = compare_map(out, "plane_map", 10961)
    wide = compare_map(out, "plane_wide", 38801)
    assert wide["domain"] == {"Re w": [-2, 2], "Im w": [34, 40]}
    run(ATLAS / "plane_anchors.py", out, "--output", out)
    run(ATLAS / "phase_lift.py", out, "--repo", ROOT, "--out", out / "phase_lift.json")
    for name in ("plane_anchors.json", "phase_lift.json"):
        compare(read(out / name), read(ATLAS / name), name)
    run(ATLAS / "resolve_staircase.py", out, "--output", out)
    review = read(out / "staircase.json")
    compare(review, read(ATLAS / "staircase.json"), "staircase.json")
    with np.load(out / "plane_map.npz", allow_pickle=False) as cells:
        rejected = set(zip(*np.nonzero(~cells["accepted"])))
    assert rejected == {(item["row"], item["column"]) for item in review["entries"]}
    assert len(review["entries"]) == len(rejected) == 37
    assert all(arb(item["length"]) > 0 for item in review["entries"])
    run(ATLAS / "gray_locus.py", out, "--out", out / "gray_locus.json")
    incidence = read(out / "gray_locus.json")
    assert incidence["source_grid_sha256"] == sha256((ATLAS / "plane_map.npz").read_bytes()).hexdigest()
    assert incidence["original_gray_count"] == incidence["inside_square_certificates"] == 37
    assert len(incidence["pixel_checks"]) == 37
    assert {(p["row"], p["column"]) for p in incidence["pixel_checks"]} == rejected
    assert all(p["arc"] == 1 and p["source_pixel_contains_level_preimage"] for p in incidence["pixel_checks"])
    # Fix the archived rational shifts for the sheet and collision comparison.
    archived_cases = read(ATLAS / "gray_collision.json")["illustrated_pixels"]
    archived_inputs = read(ATLAS / "gray_locus.json")["pixel_checks"]
    for inp, case in zip(archived_inputs, archived_cases, strict=True):
        assert (inp["row"], inp["column"]) == (case["row"], case["col"])
        h = (Fraction(inp["shift"]) - Fraction(1, 6)) * 180
        assert arb(case["collision_h"]).contains(arb(h.numerator) / h.denominator)
    run(ATLAS / "gray_collision.py", out, "--locus", ATLAS / "gray_locus.json",
        "--out", out / "gray_collision.json")
    collision = read(out / "gray_collision.json")
    compare(collision, read(ATLAS / "gray_collision.json"), "gray_collision.json")
    curve = collision["critical_curve"]
    assert curve["matched_pixel_critical_points"] == 37 and arb(curve["lower_Re_Hb_along_branch"]) > 196
    cases = collision["illustrated_pixels"]
    assert len(cases) == 37 and {(e["row"], e["col"]) for e in cases} == rejected
    assert all(e["sqrt_t_sheet_sign"] == -1 for e in cases)
    assert all(arb(e["rouche_main_lower"]) > arb(e["rouche_error_upper"]) for e in cases)
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
