"""Replay the archived 2026-11-16 Super Zeta computations in a new directory."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from verify_archive import verify_snapshot

SNAPSHOT = Path(__file__).resolve().parents[1] / "archive/2026-11-16-super-zeta-v001"
PROGRAMS = (
    "verify_superzeta_residues.py",
    "verify_residue_period.py",
    "verify_binomial_normalization.py",
    "verify_signed_histories.py",
    "verify_balanced_charge.py",
    "verify_laplace_barnes.py",
    "review_root_coefficients.py",
    "review_numerical_scopes.py",
    "make_figures.py",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="new scratch directory")
    args = parser.parse_args()
    destination = args.destination.resolve()
    archive = SNAPSHOT.parent
    if destination == archive or destination.is_relative_to(archive):
        parser.error("Choose a destination outside the archive directory.")
    verify_snapshot(SNAPSHOT)
    shutil.copytree(SNAPSHOT, destination)
    computations = destination / "computations"
    env = dict(os.environ, MPLBACKEND="Agg", PYTHONIOENCODING="utf-8")
    results = []
    for program in PROGRAMS:
        print(f"Running {program}", flush=True)
        try:
            process = subprocess.run(
                [sys.executable, str(computations / program)],
                cwd=destination,
                env=env,
                capture_output=True,
                encoding="utf-8",
                timeout=60,
            )
        except subprocess.TimeoutExpired:
            results.append({"program": program, "error": "Timed out after 60 seconds"})
            break
        results.append({
            "program": program,
            "exit_code": process.returncode,
            "stdout": process.stdout,
            "stderr": process.stderr,
        })
        if process.returncode:
            print(process.stderr, file=sys.stderr)
            break
    passed = len(results) == len(PROGRAMS) and all(row.get("exit_code") == 0 for row in results)
    (destination / "new-replay-results.json").write_text(
        json.dumps({"passed": passed, "programs": results}, indent=2) + "\n",
        encoding="utf-8",
    )
    if not passed:
        raise SystemExit("Replay stopped early or failed. See new-replay-results.json.")
    print(f"{len(results)} programs passed. Replay copy saved to {destination}")


if __name__ == "__main__":
    main()
