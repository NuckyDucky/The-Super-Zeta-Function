"""Replay the sixth-zero fold and build its static graph with Python 3.12 and python-flint 0.9.0."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile


SNAPSHOT = Path(__file__).resolve().parents[1] / "archive" / "2026-11-19-sixth-passes-v001"


def build(output):
    output.mkdir(parents=True, exist_ok=True)
    # The web version is rendered from the newly checked values. Keep the archived
    # reference and any previously published page intact if verification fails.
    with tempfile.TemporaryDirectory(dir=output) as temp:
        scratch = Path(temp)
        data = scratch / "jets.json"
        page = scratch / "index.html"
        turning = scratch / "turning.json"
        for verifier, result in [("verify.py", data), ("turning.py", turning)]:
            subprocess.run([
                sys.executable, "-B", str(SNAPSHOT / "compute" / verifier),
                "--output", str(result), "--compare", str(SNAPSHOT / "compute" / result.name),
            ], check=True)
        subprocess.run([
            sys.executable, "-B", str(SNAPSHOT / "view" / "build.py"),
            "--data", str(data), "--output", str(page),
        ], check=True)
        data.replace(output / data.name)
        turning.replace(output / turning.name)
        page.replace(output / page.name)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path, help="Directory for the page and its checked data")
    build(parser.parse_args().output.resolve())
