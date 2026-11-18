"""Replay an experiment in an empty temporary directory from this checkout."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent
MATCH = ARCHIVE / "2026-11-17-dottie-grid-match-v001"
OFFCENTER = ARCHIVE / "2026-11-17-offcenter-superzeta-v001"
RETURNS = ARCHIVE / "2026-11-17-quartet-return-recursion-v001" / "computations"
FOUNDATION = ARCHIVE / "2026-11-16-super-zeta-v001" / "computations"
MODES = ("contour", "factorial", "layers", "native-angle", "high-angle")


def run(mode):
    if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):
        raise RuntimeError("The interval and contour checks require Python assertions.")
    env = os.environ.copy()
    search = [str(p) for p in (MATCH, OFFCENTER, RETURNS, FOUNDATION)]
    if env.get("PYTHONPATH"):
        search.append(env["PYTHONPATH"])
    env["PYTHONPATH"] = os.pathsep.join(search)
    with TemporaryDirectory(prefix="quartet-angle-") as tmp:
        scratch = Path(tmp)
        def execute(name, *args, capture=False):
            script = scratch / name
            shutil.copyfile(HERE / name, script)
            result = subprocess.run([sys.executable, "-B", str(script), *args],
                                    cwd=scratch, env=env, check=True,
                                    stdout=subprocess.PIPE if capture else None)
            return result.stdout

        if mode in ("contour", "high-angle"):
            shutil.copyfile(MATCH / "dottie-grid-certificate.json",
                            scratch / "dottie-grid-certificate.json")
        if mode == "contour":
            for command, record in (("freeze", "dottie-second-harmonic-plan.json"),
                                    ("count", "dottie-second-harmonic-count.json")):
                execute("dottie_second_harmonic_overlap.py", command, capture=True)
                saved = json.loads((HERE / record).read_bytes())
                regenerated = json.loads((scratch / record).read_bytes())
                if saved != regenerated:
                    raise ValueError(f"Replay differs from {record}")
                print(f"Reproduced {record}", flush=True)
        elif mode == "high-angle":
            shutil.copyfile(HERE / "dottie-second-harmonic-count.json",
                            scratch / "dottie-second-harmonic-count.json")
            execute("dottie_local_angle.py")
        elif mode == "native-angle":
            shutil.copyfile(HERE / "track_native_superzeta_layers.py",
                            scratch / "track_native_superzeta_layers.py")
            execute("native_zero_angle_step.py")
        elif mode == "layers":
            execute("track_native_superzeta_layers.py", "--certify", "--ratios")
        elif mode == "factorial":
            execute("dottie_factorial_phase.py")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=(*MODES, "all"), default="all", nargs="?")
    selected = parser.parse_args().mode
    for mode in MODES if selected == "all" else (selected,):
        run(mode)
