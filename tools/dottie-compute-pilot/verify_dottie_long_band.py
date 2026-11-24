"""Kernel-check one prepared long Dottie band in resumable single-worker blocks.

Run next to the generated Lean sources. The caller supplies the pinned Lean
binary and a LEAN_PATH containing DottieBandLucasCheck and DottieBandChunkReplay.
A receipt is written only after the source, build, and theorem axiom audit pass.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import uuid


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DIRECT_IMPORTS = ("DottieBandLucasCheck.olean", "DottieBandChunkReplay.olean")
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check_index(path):
    index = json.loads(path.read_text(encoding="utf-8"))
    band = index["band"]
    if index["format"] != "dottie-long-band-sources-v1" or band not in (1, 2, 3):
        raise ValueError("Expected a prepared archived long-band index")
    records = index["blocks"]
    archive = index["archive"]
    first = next_begin = int(archive["begin"])
    total = lower = upper = 0
    if not records or not 1 <= index["block_size"] <= 4096:
        raise ValueError("The index must have blocks of up to 4096 rows")
    for num, record in enumerate(records, 1):
        expected_module = f"DottieLongBand{band}Block{num:06d}"
        last = int(record["end"])
        if (record["number"] != num or record["module"] != expected_module
                or record["file"] != f"{expected_module}.lean"
                or int(record["begin"]) != next_begin
                or last - next_begin + 1 != record["rows"]
                or not 1 <= record["rows"] <= index["block_size"]
                or (record["rows"] != index["block_size"] and num != len(records))):
            raise ValueError(f"Invalid contiguous block {num}")
        next_begin = last + 1
        summary = record["expected"]
        lower = min(lower, total + summary["min_prefix"])
        upper = max(upper, total + summary["max_prefix"])
        total += summary["sum"]
    assembly = index["assembly"]
    complete = next_begin - 1 == int(archive["end"])
    if (assembly["module"] != f"DottieLongBand{band}Assembly"
            or assembly["file"] != f"{assembly['module']}.lean"
            or int(assembly["begin"]) != first or int(assembly["end"]) != next_begin - 1
            or assembly["rows"] != next_begin - first
            or next_begin - 1 > int(archive["end"])
            or index["complete_archive_interval"] != complete
            or assembly["expected"] != {"sum": total, "min_prefix": lower, "max_prefix": upper}
            or (complete and assembly["coefficient_sha256"] != archive["coefficient_sha256"])):
        raise ValueError("The assembly does not match the contiguous blocks")
    return index


def compiler(lean, folder):
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    search = [Path(value).resolve() for value in env.get("LEAN_PATH", "").split(os.pathsep) if value]
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [folder, *search])
    dependencies = {}
    for name in DIRECT_IMPORTS:
        candidate = next((p / name for p in search if (p / name).is_file()), None)
        if candidate is None:
            raise OSError(f"LEAN_PATH is missing {name}")
        dependencies[name] = sha256(candidate)
    lean_path = Path(shutil.which(lean) or lean).resolve()
    ver = subprocess.run([str(lean_path), "--version"], env=env, check=True, text=True,
                         capture_output=True, creationflags=NO_WINDOW)
    version = ver.stdout.strip()
    if not version.startswith("Lean (version 4.33.1,"):
        raise ValueError(f"Unexpected Lean version: {version}")
    return lean_path, env, {"version": version, "lean_sha256": sha256(lean_path),
                            "proof_import_sha256": dependencies}


def audit_theorem(theorem, log):
    found = re.search(r"'" + re.escape(theorem) + r"' depends on axioms:\s*\[([^\]]+)\]", log)
    if found:
        axioms = found.group(1).replace("\n", " ").replace("\r", "").split(",")
        axioms = [a.strip() for a in axioms]
        if axioms and set(axioms) <= ALLOWED_AXIOMS:
            return axioms
    raise ValueError("Missing or unexpected axiom audit for " + theorem)


def verified_receipt(receipt, olean, expected):
    if not (receipt.is_file() and olean.is_file()):
        return False
    try:
        saved = json.loads(receipt.read_text(encoding="utf-8"))
        return (all(saved.get(k) == v for k, v in expected.items())
                and bool(saved["axioms"]) and set(saved["axioms"]) <= ALLOWED_AXIOMS
                and sha256(olean) == saved["olean_sha256"])
    except (KeyError, TypeError, ValueError, OSError):
        return False


def verify_source(folder, record, theorem, lean, env, context, *, resume, parent_receipts=None):
    name = record["module"]
    source = folder / record["file"]
    digest = record["source_sha256"]
    if source.stat().st_size != record["source_bytes"] or sha256(source) != digest:
        raise ValueError(f"Source bytes differ from the prepared index for {name}")
    out = folder / f"{name}.olean"
    log_path = folder / f"{name}-build.txt"
    receipt = folder / f"{name}-receipt.json"
    expected = {**context, "module": name, "range": [record["begin"], record["end"]],
                "theorem": theorem, "source_sha256": digest}
    if parent_receipts is not None:
        expected["block_olean_sha256"] = parent_receipts
    if resume and verified_receipt(receipt, out, expected):
        print(f"{name} reused ({record['rows']} norms)", flush=True)
        return json.loads(receipt.read_text(encoding="utf-8"))["olean_sha256"]
    nonce = uuid.uuid4().hex
    pending = folder / f".{name}-{nonce}.olean"
    pending_receipt = folder / f".{name}-{nonce}.json"
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            [str(lean), "-j", "1", "-s", "65536", "-DwarningAsError=true",
             "-o", str(pending), source.name], cwd=folder, env=env,
            capture_output=True, text=True, encoding="utf-8", creationflags=NO_WINDOW,
        )
        log = proc.stdout + proc.stderr
        log_path.write_text(log, encoding="utf-8")
        if proc.returncode != 0 or sha256(source) != digest:
            raise RuntimeError(f"Lean or source integrity check failed for {name}. See {log_path}")
        axioms = audit_theorem(theorem, log)
        olean_digest = sha256(pending)
        pending.replace(out)
        seconds = time.perf_counter() - start
        result = {**expected, "axioms": axioms, "olean_sha256": olean_digest, "seconds": seconds}
        pending_receipt.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        pending_receipt.replace(receipt)
        print(f"{name} passed ({record['rows']} norms, {seconds:.3f} s)", flush=True)
        return olean_digest
    finally:
        pending.unlink(missing_ok=True)
        pending_receipt.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("index", type=Path, help="DottieLongBandNIndex.json from the source generator")
    parser.add_argument("--lean", default="lean", help="path to the pinned Lean executable")
    parser.add_argument("--through-block", type=int, help="stop after this many leading blocks")
    parser.add_argument("--resume", action="store_true", help="reuse matching checked block receipts")
    args = parser.parse_args()
    try:
        index = check_index(args.index)
        folder = args.index.resolve().parent
        blocks = index["blocks"]
        through = len(blocks) if args.through_block is None else args.through_block
        if not 1 <= through <= len(blocks):
            raise ValueError("--through-block is outside the prepared range")
        lean, env, context = compiler(args.lean, folder)
        hashes = {}
        for record in blocks[:through]:
            theorem = f"QuarticModel.DottieBandBlock{record['begin']}_{record['rows']}.certificate"
            hashes[record["module"]] = verify_source(
                folder, record, theorem, lean, env, context, resume=args.resume)
        if through == len(blocks):
            assembly = index["assembly"]
            verify_source(folder, assembly, f"QuarticModel.{assembly['module']}.certificate",
                          lean, env, context, resume=args.resume, parent_receipts=hashes)
    except (OSError, KeyError, TypeError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
