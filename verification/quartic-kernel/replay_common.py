"""Locate the pinned toolchain and unpack the frozen Lean sources."""

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from zipfile import ZipFile


PACKET = Path(__file__).resolve().parent
REPO = PACKET.parents[1]
PROJECT = REPO / "lean"
BUILD = PACKET / ".replay"
GENERATED = BUILD / "generated"
SOURCE_ROOTS = (PACKET / "source", GENERATED, REPO / "lean-quartic-orders", PROJECT)
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
KERNEL_PASS = "The kernel certificate passed the standard-axioms-only audit."
SHARD_COUNTS = {"KernelNumerics": 6705, "KernelPrefixes": 181, "KernelCells": 66}
BASE_SHA = "9dd0d13acb6e1925ca8939dfad43683d55a521bd"


def unpack_generated():
    archive = PACKET / "generated-sources.zip"
    checksum = (PACKET / "generated-sources.sha256").read_text(encoding="ascii").strip()
    if hashlib.sha256(archive.read_bytes()).hexdigest() != checksum:
        raise ValueError("Generated Lean source archive checksum mismatch.")
    with ZipFile(archive) as bundle:
        entries = bundle.namelist()
        if any(not re.fullmatch(r"(KernelNumerics/Block\d+Part\d+|Kernel(?:Prefixes|Cells)/Block\d+)\.lean", name)
               for name in entries):
            raise ValueError("Unexpected generated Lean archive entry.")
        if len(set(entries)) != len(entries) or Counter(name.split("/")[0] for name in entries) != SHARD_COUNTS:
            raise ValueError("Unexpected generated Lean module counts.")
        for name in entries:
            target = GENERATED / name
            contents = bundle.read(name)
            if not target.is_file() or target.read_bytes() != contents:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(contents)
    for folder in SHARD_COUNTS:
        if {path.relative_to(GENERATED).as_posix() for path in (GENERATED / folder).glob("*.lean")} - set(entries):
            raise ValueError(f"Unexpected Lean source in {GENERATED / folder}.")


def add_lean_options(parser):
    parser.add_argument("--lake-project", type=Path, default=PROJECT,
                        help="Lake project with the same manifest and toolchain and a populated Mathlib cache")
    parser.add_argument("--lean", type=Path, help="Lean executable if already installed outside elan")


def lean_environment(lake_project, executable):
    lake_project = lake_project.resolve()
    manifest = "lake-manifest.json"
    if (json.loads((lake_project / manifest).read_text(encoding="utf-8")) !=
        json.loads((PROJECT / manifest).read_text(encoding="utf-8")) or
        (lake_project / "lean-toolchain").read_text().strip() != (PROJECT / "lean-toolchain").read_text().strip()):
        raise ValueError("The cache project must match this repository's manifest and toolchain.")
    if executable:
        lean = executable.resolve()
    else:
        prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                         cwd=lake_project, text=True, encoding="utf-8").strip()
        lean = Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    version = subprocess.check_output([lean, "--version"], text=True, encoding="utf-8")
    if "version 4.19.0," not in version:
        raise ValueError("This replay requires Lean 4.19.0.")
    packages = lake_project / ".lake/packages"
    libraries = [path / ".lake/build/lib/lean" for path in sorted(packages.iterdir())
                 if (path / ".lake/build/lib/lean").is_dir()]
    if not libraries:
        raise ValueError("Populate the pinned Mathlib cache with lake exe cache get.")
    return lean, version, libraries
