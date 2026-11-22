"""Compile the quartic order theorem from source and audit its Lean axioms."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


PACKET = Path(__file__).resolve().parent
PROJECT = PACKET.parent / "lean"
ENTRIES = ("QuarticSignedOrders", "OrderedSignControl")


def source_path(module):
    relative = Path(*module.split(".")).with_suffix(".lean")
    for root in (PACKET, PROJECT):
        path = root / relative
        if path.is_file():
            return path
    return None


def dependencies(roots):
    local = {}
    imports = set()

    def visit(module):
        if module in local or module in imports:
            return
        source = source_path(module)
        if source is None:
            if module.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init"}:
                raise ValueError(f"Missing project source: {module}")
            imports.add(module)
            return
        for line in source.read_text(encoding="utf-8-sig").splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    visit(dep)
        local[module] = source

    for root in roots:
        visit(root)
    return local, imports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true",
                        help="fetch pinned mathlib imports before compiling")
    parser.add_argument("--lake-project", type=Path, default=PROJECT,
                        help="reuse the Lake environment of a checkout with the identical lockfile")
    args = parser.parse_args()
    cache_project = args.lake_project.resolve()
    manifest = "lake-manifest.json"
    if (json.loads((cache_project / manifest).read_text(encoding="utf-8")) !=
        json.loads((PROJECT / manifest).read_text(encoding="utf-8")) or
        (cache_project / "lean-toolchain").read_text().strip() !=
        (PROJECT / "lean-toolchain").read_text().strip()):
        parser.exit(1, "The cache project must match the submission's manifest and toolchain.\n")
    local, imports = dependencies(ENTRIES)
    lake = shutil.which("lake")
    if not lake:
        parser.exit(1, "Install elan or put the pinned Lake binary on PATH.\n")
    if args.fetch_cache:
        modules = sorted(m for m in imports if m.startswith("Mathlib."))
        subprocess.run([lake, "exe", "cache", "get", *modules], cwd=cache_project, check=True)
    def lake_env(*argv):
        return subprocess.check_output([lake, "env", *argv], cwd=cache_project,
                                       text=True, encoding="utf-8").strip()
    lean_path = lake_env(sys.executable, "-c", "import os; print(os.environ['LEAN_PATH'])")
    project_objects = (cache_project / ".lake/build/lib/lean").resolve()
    paths = ((cache_project / p).resolve() for p in lean_path.split(os.pathsep) if p)
    libs = [str(path) for path in paths if path != project_objects]
    # Resolve the binary within the selected toolchain before entering the scratch directory.
    lean = Path(lake_env("lean", "--print-prefix")) / "bin" / (
        "lean.exe" if os.name == "nt" else "lean"
    )
    if "version 4.19.0," not in subprocess.check_output([lean, "--version"], text=True):
        parser.exit(1, "The checked sources require Lean 4.19.0.\n")
    with tempfile.TemporaryDirectory(prefix="quartic-orders-") as scratch:
        stage = Path(scratch).resolve()
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(stage), *libs]))
        for name, source in local.items():
            relative = Path(*name.split(".")).with_suffix(".lean")
            dest = stage / relative
            dest.parent.mkdir(exist_ok=True, parents=True)
            shutil.copyfile(source, dest)
            print(f"Checking {name}", flush=True)
            subprocess.run([lean, "-o", str(relative.with_suffix(".olean")), str(relative)],
                           cwd=stage, env=env, check=True)
        audit = (PACKET / "Audit.template").read_text(encoding="utf-8")
        audit = "\n".join(f"import {name}" for name in ENTRIES[1:]) + "\n" + audit
        # Lean names here come exclusively from module-path tokens in the repository.
        if not all(re.fullmatch(r"[\w.]+", name) for name in local):
            raise ValueError("Unexpected project module name")
        audit = audit.replace("MODULES", ", ".join("`" + name for name in local))
        (stage / "Audit.lean").write_text(audit, encoding="utf-8")
        subprocess.run([lean, "-DwarningAsError=true", "Audit.lean"], cwd=stage,
                       env=env, check=True)


if __name__ == "__main__":
    main()
