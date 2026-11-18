"""Build the pinned proof library and audit theorem dependencies with Lean."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess


PROJECT = Path(__file__).resolve().parents[1] / "lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true",
                        help="download precompiled mathlib imports for the pinned revision")
    args = parser.parse_args()
    env = os.environ.copy()
    workspace_bin = PROJECT.parent / ".lean-tools" / "lean-4.19.0-windows" / "bin"
    if (workspace_bin / "lake.exe").is_file():
        env["PATH"] = str(workspace_bin) + os.pathsep + env.get("PATH", "")
    lake = shutil.which("lake", path=env.get("PATH"))
    if lake is None:
        parser.exit(1, "Install elan from https://lean-lang.org/install/ and reopen the terminal.\n")
    modules = set()
    for source in (PROJECT / "SuperZeta").glob("*.lean"):
        modules.update(line.split()[1] for line in source.read_text(encoding="utf-8").splitlines()
                       if line.startswith("import Mathlib."))
    if args.fetch_cache:
        subprocess.run([lake, "exe", "cache", "get", *sorted(modules)], cwd=PROJECT, env=env, check=True)
    subprocess.run([lake, "build"], cwd=PROJECT, env=env, check=True)
    subprocess.run([lake, "env", "lean", "Audit.lean"], cwd=PROJECT, env=env, check=True)


if __name__ == "__main__":
    main()
