"""Inside the pinned project's lean directory: lake env python PATH/check_triadic.py."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / "Dottie-Forward-Iteration"))
from check_forward import verify

with tempfile.TemporaryDirectory(prefix="triadic-check-") as tmp:
    scratch = Path(tmp)
    verify(scratch, False)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(scratch) + os.pathsep + env["LEAN_PATH"]
    checked = subprocess.check_output(
        [shutil.which("lean"), "-DwarningAsError=true", str(here / "TriadicStart.lean")],
        env=env, text=True, encoding="utf-8")
    for name in ("triadic_ne_dyadic", "start_only"):
        expected = f"'DottieOriented.TriadicStart.{name}' depends on axioms: ["
        deps = checked.split(expected, 1)[1].split("]", 1)[0].split(", ")
        assert set(deps) == {"propext", "Classical.choice", "Quot.sound"}
    print(checked, end="")
