"""Rebuild the public proof chain using the kernel-checked certificate."""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import contextmanager
from pathlib import Path
import argparse
import errno
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time


from replay_common import (AXIOMS as STANDARD_AXIOMS, BASE_SHA, BUILD, KERNEL_PASS, PACKET, PROJECT,
                           SOURCE_ROOTS, add_lean_options, lean_environment, unpack_generated)


KERNEL_TARGETS = {
    "QuarticKernel.actual_checked_shells_kernel",
    "QuarticKernel.actual_cells_kernel",
    "QuarticKernel.actual_quartic_certificate_kernel",
    "QuarticKernel.verified_quartic_direction_kernel",
    "QuarticKernel.verified_quartic_zero_on_line_kernel",
}


def sources_for(*entries):
    sources = {}
    seen = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        if module.split(".")[0] in {"Mathlib", "Lean", "Init", "Std", "Batteries"}:
            return
        relative = Path(*module.split(".")).with_suffix(".lean")
        path = next((root / relative for root in SOURCE_ROOTS if (root / relative).is_file()), None)
        if path is None:
            raise RuntimeError(f"Missing source for {module}")
        source = path.read_bytes()
        imports = tuple(dep for line in re.findall(
            r"^import\s+([^\r\n]+)", source.decode("utf-8-sig"), re.M
        ) for dep in line.split("--", 1)[0].split())
        for dep in imports:
            visit(dep)
        sources[module] = (path, source, imports)

    for name in entries:
        visit(name)
    return sources


@contextmanager
def replay_lock(path, revision):
    with path.open("x", encoding="utf-8") as lock:
        lock.write(revision + "\n")
    try:
        yield
    finally:
        path.unlink()


def kernel_running(lock_path):
    if not lock_path.is_file():
        return False
    with lock_path.open("r+b") as lock:
        try:
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            if exc.errno not in {errno.EACCES, errno.EAGAIN}:
                raise
            return True
    return False


def await_kernel_pass(checkpoint, log):
    print(f"Waiting for the Lean certificate build at {checkpoint}.", flush=True)
    while kernel_running(checkpoint / ".replay.lock"):
        time.sleep(15)
    # replay.py closes its lock immediately before writing the final transcript.
    for _ in range(10):
        if log.is_file():
            transcript = log.read_text(encoding="utf-8")
            if KERNEL_PASS in transcript.splitlines():
                return transcript
        time.sleep(1)
    raise RuntimeError(f"The certificate replay stopped before its final axiom audit passed. See {log}.")


def axioms_from(output):
    result = {name: {item.strip() for item in axioms.split(",") if item.strip()}
              for name, axioms in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.M)}
    result.update((name, set()) for name in re.findall(r"^'([^']+)' does not depend on any axioms", output, re.M))
    return result


def checked_artifact_reports(checkpoint, sources, libs, runtime, entry):
    keys, receipt_reports = {}, {}

    def file_digest(path):
        with path.open("rb") as file:
            return hashlib.file_digest(file, "sha256").hexdigest()

    def key_for(module):
        if module in keys:
            return keys[module]
        relative = Path(*module.split(".")).with_suffix(".lean")
        if module not in sources:
            external = next((lib / relative.with_suffix(".olean") for lib in libs
                             if (lib / relative.with_suffix(".olean")).is_file()), None)
            if external is None:
                raise RuntimeError(f"Missing checked package module {module}.")
            digest = file_digest(external)
        else:
            _, source, imports = sources[module]
            destination = checkpoint / relative
            if destination.read_bytes() != source:
                raise RuntimeError(f"Current full-proof source differs from the checked source for {module}.")
            inputs = [runtime, hashlib.sha256(source).hexdigest(), *(key_for(dep) for dep in imports)]
            digest = hashlib.sha256("\n".join(inputs).encode()).hexdigest()
            receipt = json.loads(destination.with_suffix(".verified.json").read_text(encoding="utf-8"))
            artifact = destination.with_suffix(".olean")
            if receipt["input"] != digest or receipt["artifact"] != file_digest(artifact):
                raise RuntimeError(f"Invalid checked artifact or dependency fingerprint for {module}.")
            receipt_reports.update(axioms_from(receipt["output"]))
        keys[module] = digest
        return digest

    key_for(entry)
    if not sources.keys() <= keys.keys():
        raise RuntimeError("Some certificate modules were outside the checked artifact closure.")
    return receipt_reports


def check_kernel_artifacts(checkpoint, sources, libs, runtime, transcript):
    reports = axioms_from(transcript)
    for target in sorted(KERNEL_TARGETS):
        if target not in reports or not reports[target] <= STANDARD_AXIOMS:
            raise RuntimeError(f"Missing standard-axioms-only audit for {target}.")
    receipt_reports = checked_artifact_reports(checkpoint, sources, libs, runtime, "QuarticVerifiedKernel")
    for target in sorted(KERNEL_TARGETS):
        if receipt_reports.get(target) != reports[target]:
            raise RuntimeError(f"The checked artifact disagrees with the final axiom audit for {target}.")
        print(f"Checked input {target} [{', '.join(sorted(reports[target]))}]", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_lean_options(parser)
    parser.add_argument("--checkpoint", type=Path, default=BUILD / "certificate")
    parser.add_argument("--certificate-log", type=Path, default=BUILD / "certificate.log")
    parser.add_argument("--jobs", type=int, default=1)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--audit-only", action="store_true", help="Check the complete certificate receipt chain")
    mode.add_argument("--smoke", action="store_true", help="Check the three-point quartic example in Lean")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    checkpoint = args.checkpoint.resolve()
    unpack_generated()
    pin, runtime, libs = lean_environment(args.lake_project, args.lean)
    entries = ("QuarticStageCertificate", "QuarticCrossAnalysis", "StageAudit")
    certificate_sources = sources_for("QuarticVerifiedKernel")
    sources = sources_for(*entries, "QuarticVerifiedKernel")
    transcript = await_kernel_pass(checkpoint, args.certificate_log)
    check_kernel_artifacts(checkpoint, certificate_sources, libs, runtime, transcript)
    if args.audit_only:
        print(f"Verified source, output and dependency digests for {len(certificate_sources)} certificate modules.")
        return
    if args.smoke:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [checkpoint, *libs])), LEAN_NUM_THREADS="1")
        subprocess.run([pin, "-j", "1", "-s", "65536", "-DwarningAsError=true", "source/Smoke.lean"],
                       cwd=PACKET, env=env, check=True)
        return
    stage = Path(tempfile.mkdtemp(prefix="full-chain-kernel-", dir=BUILD))
    print(f"Base {BASE_SHA}. Frozen source import closure: {len(sources)} modules.", flush=True)
    print(f"Build directory: {stage}", flush=True)
    worker_count = args.jobs
    source_keys = {}
    for module, (_, source, imports) in sources.items():
        key = hashlib.sha256(source)
        key.update(runtime.strip().encode())
        key.update((PROJECT / "lake-manifest.json").read_bytes())
        for dep in imports:
            if dep in source_keys:
                key.update(source_keys[dep].encode())
        source_keys[module] = key.hexdigest()
    with replay_lock(stage / ".replay.lock", BASE_SHA):
        search = [stage, checkpoint, *libs]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, search)),
                   LEAN_NUM_THREADS="1")
        waiting = {module: value for module, value in sources.items() if module not in certificate_sources}
        for module, (_, source, _) in waiting.items():
            relative = Path(*module.split(".")).with_suffix(".lean")
            destination = stage / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(source)

        # Lean 4.19 resolves a package directory at the first matching search
        # root. Put the verified objects for split packages in that same root.
        for module in certificate_sources:
            components = module.split(".")
            if len(components) > 1 and (stage / components[0]).is_dir():
                relative = Path(*components).with_suffix(".olean")
                destination = stage / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(checkpoint / relative, destination)

        def build(module):
            path, source, _ = sources[module]
            relative = Path(*module.split(".")).with_suffix(".lean")
            receipt = stage / relative.with_suffix(".verified")
            olean = stage / relative.with_suffix(".olean")
            digest = hashlib.sha256(source).hexdigest()
            if olean.is_file() and receipt.is_file() and receipt.read_text() == source_keys[module]:
                print(f"Reusing verified {module}  sha256={digest}", flush=True)
                return
            print(f"Checking {module}  sha256={digest}  from {path}", flush=True)
            options = ["-j", "1", "-s", "65536"]
            subprocess.run([pin, *options, "-DwarningAsError=true", "-o", relative.with_suffix(".olean"),
                            relative], cwd=stage, env=env, check=True)
            receipt.write_text(source_keys[module], encoding="utf-8")

        completed = set(certificate_sources)
        in_progress = {}
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            while waiting or in_progress:
                reachable = (
                    module for module, (_, _, imports) in waiting.items()
                    if all(dep not in sources or dep in completed for dep in imports)
                )
                ready = list(reachable)[:worker_count - len(in_progress)]
                for module in ready:
                    del waiting[module]
                    in_progress[pool.submit(build, module)] = module
                if not in_progress:
                    raise RuntimeError("The import graph contains a cycle.")
                done, _ = wait(in_progress, return_when=FIRST_COMPLETED)
                for future in done:
                    future.result()
                    completed.add(in_progress.pop(future))
    print(f"All {len(sources)} modules in the combined import closure passed.", flush=True)
    print(f"Clean full-proof replay passed: {len(sources) - len(certificate_sources)} modules built from source "
              f"using {len(certificate_sources)} verified certificate modules.", flush=True)


if __name__ == "__main__":
    main()
