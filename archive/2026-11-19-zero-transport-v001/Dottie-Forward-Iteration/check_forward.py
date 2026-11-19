"""Run from the pinned project's lean directory via lake env python check_forward.py."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def verify(scratch, resume):
    here = Path(__file__).resolve().parent
    prior = here.parent / "Dottie-Second-Zero"
    lean = shutil.which("lean")
    if not lean or "LEAN_PATH" not in os.environ:
        raise RuntimeError("Run inside lake env in The-Super-Zeta-Function/lean.")
    scratch.mkdir(exist_ok=True, parents=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(scratch) + os.pathsep + env["LEAN_PATH"]
    for name, root in [("FlankReferences",prior),("ReferenceReset",prior),
                       ("ForwardCertificate",here),("VerifyForward",here)]:
        source = root / (name+".lean")
        olean = scratch / (name+".olean")
        if resume and name in ("FlankReferences","ReferenceReset") and olean.is_file():
            continue
        subprocess.run([lean, "-DwarningAsError=true", "--root="+str(root),
                        "-o", str(olean), str(source)],env=env,check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--scratch", type=Path)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.scratch:
        verify(args.scratch.resolve(),args.resume)
    else:
        with tempfile.TemporaryDirectory() as scratch:
            verify(Path(scratch),False)
