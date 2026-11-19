"""From the pinned project's lean directory, run lake env python /path/to/check_reset.py.

Build the public project dependencies SuperZeta.Oriented.LiuConnection and
SuperZeta.Multiplicity first. Temporary compiled files never enter the archive.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

base = Path(__file__).resolve().parent
lean = shutil.which("lean")
if not lean or not os.environ.get("LEAN_PATH"):
    raise SystemExit("Run this script from the project's lean directory using lake env python.")

with tempfile.TemporaryDirectory(prefix="dottie-reset-") as scratch:
    env = dict(os.environ)
    env["LEAN_PATH"] = scratch + os.pathsep + env["LEAN_PATH"]
    compiler = [lean, "-DwarningAsError=true", f"--root={base}"]
    for module in ("FlankReferences","ReferenceReset"):
        subprocess.run(compiler + ["-o",str(Path(scratch)/(module+".olean")),
                                   str(base/(module+".lean"))], env=env, check=True)
    audit = Path(scratch)/"AuditReset.lean"
    theorems = ["resetFactor_entire","reset_identity","endpoint_reenters","starting_zero_iff"]
    audit.write_text("import ReferenceReset\n" + "".join(
        f"#print axioms DottieOriented.ReferenceReset.{name}\n" for name in theorems),
        encoding="utf-8")
    subprocess.run([lean, "-DwarningAsError=true",str(audit)], env=env, check=True)
