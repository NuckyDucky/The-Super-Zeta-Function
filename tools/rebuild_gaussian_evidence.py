"""Regenerate the 193 Gaussian moment records and replay the published circle proofs."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from gaussian_moments import regenerate
from verify_archive import verify_snapshot


ARCHIVE = Path(__file__).resolve().parents[1] / "archive"
CIRCLES = "2026-11-20-gaussian-circle-phases-v001"
BLOCKS = "2026-11-20-gaussian-relative-remainder-v001"
SECTOR = "2026-11-20-gaussian-common-sector-v001"

# Keep the sibling paths used in the original proofs. The published moment
# table is a comparison target for regenerate(), never an input to the replay.
INPUTS = {
    "2026-11-19-dottie-plane-atlas-v001": ("atlas/phase_lift.json",),
    "2026-11-20-gaussian-reflected-disks-v001": ("gaussian_inputs.py", "arc-gaussian.py"),
    CIRCLES: ("replay.py", "replay_tail.py", "tail-bound.json"),
    BLOCKS: ("verify.py",),
    SECTOR: ("verify_sector.py",),
}
CHECKS = (
    (CIRCLES, "replay.py", "Winding and phase on both complete circles"),
    (CIRCLES, "replay_tail.py", "Absolute bound for the full remainder"),
    (BLOCKS, "verify.py", "Direction and size of the 192 adjacent changes"),
    (SECTOR, "verify_sector.py", "Common angular sector for all 193 cutoffs"),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=4, help="processes for the raw moments (default 4)")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    if not __debug__:
        parser.error("Run with Python assertions enabled. The published verifiers use them.")
    with tempfile.TemporaryDirectory(prefix="gaussian-moment-replay-") as directory:
        scratch = Path(directory)
        for snapshot, filenames in INPUTS.items():
            verify_snapshot(ARCHIVE / snapshot)
            for name in filenames:
                target = scratch / snapshot / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ARCHIVE / snapshot / name, target)
        regenerate(scratch / CIRCLES / "moments.json.gz", workers=args.workers)
        for snapshot, script, title in CHECKS:
            print(title, flush=True)
            subprocess.run([sys.executable, "-E", "-B", script], cwd=scratch / snapshot, check=True)
    print("All 193 cutoff records regenerated and all four published checks passed.")


if __name__ == "__main__":
    main()
