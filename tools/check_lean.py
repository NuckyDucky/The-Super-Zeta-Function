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
    sources = list((PROJECT / "SuperZeta").rglob("*.lean"))
    project_modules = {".".join(path.relative_to(PROJECT).with_suffix("").parts): path
                       for path in [PROJECT / "SuperZeta.lean", *sources]}
    modules = set()
    visited = set()
    pending = ["SuperZeta"]
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        for line in project_modules[name].read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    if dependency in project_modules:
                        pending.append(dependency)
                    elif dependency.startswith("Mathlib."):
                        modules.add(dependency)
    missing = sorted(set(project_modules) - visited)
    if missing:
        parser.exit(1, "Modules missing from the proof audit: " + ", ".join(missing) + "\n")
    if args.fetch_cache:
        subprocess.run([lake, "exe", "cache", "get", *sorted(modules)], cwd=PROJECT, env=env, check=True)
    subprocess.run([lake, "build"], cwd=PROJECT, env=env, check=True)
    subprocess.run([lake, "env", "lean", "Audit.lean"], cwd=PROJECT, env=env, check=True)


if __name__ == "__main__":
    main()
