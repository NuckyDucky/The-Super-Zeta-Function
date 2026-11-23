"""Rebuild the checked quartic lemmas and audit their Lean dependencies."""

import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from threading import Lock


from replay_common import (AXIOMS, BUILD, GENERATED, KERNEL_PASS, SOURCE_ROOTS,
                           add_lean_options, lean_environment, unpack_generated)


AUDITED = {
    "QuarticKernel.coeff_abs_le",
    "QuarticKernel.evalMark_eq",
    "QuarticKernel.checked_prefix",
    "QuarticKernel.kernel_pos_after_12",
    "QuarticKernel.kernel_pos_after_13",
    "QuarticKernel.weighted_tail",
    "QuarticKernel.rightMellin",
    "QuarticKernel.mellin_log",
    "QuarticKernel.theta_reflection_iff_kernel_even",
    "QuarticKernel.mellin_fold_of_even",
    "QuarticKernel.exponential_kernel_integrable",
    "QuarticKernel.mellin_fold_in_rectangle",
    "QuarticKernel.assemble_mellin_from_reflection_and_cells",
    "QuarticKernel.assemble_mellin_from_cells",
    "QuarticKernel.mellin_differentiable_from_center",
    "QuarticKernel.theta_quarter_lattice",
    "QuarticKernel.gaussianLattice_theta",
    "QuarticKernel.gaussAmplitude_of_center_nonzero",
    "QuarticKernel.theta_reflection_of_center_nonzero",
    "QuarticKernel.theta_head_and_tail",
    "QuarticKernel.theta_cell_bounds",
    "QuarticKernel.theta_ge_exp_sub_remainder",
    "QuarticKernel.actual_remainder_lt_first",
    "QuarticKernel.kernel_pos_of_actual_prefix",
    "QuarticKernel.compact_weight_lower",
    "QuarticKernel.direct_slope_floor",
    "QuarticKernel.direct_mellin_reading",
    "QuarticKernel.coefficient_count_bound",
    "QuarticKernel.theta_tail_abs",
    "QuarticKernel.geometric_bin",
    "QuarticKernel.complex_integrable",
    "QuarticKernel.mass_tail_lt",
    "QuarticKernel.line_tail_lt",
    "QuarticKernel.assemble_from_core",
    "QuarticDualArithmetic.dual_lattice",
    "QuarticDualArithmetic.dual_norm",
    "QuarticDualArithmetic.combined_character",
    "QuarticDualArithmetic.dual_character",
    "QuarticFiniteFourier.quarticCharacter_primitive",
    "QuarticFiniteFourier.actual_fourier_line",
    "QuarticFiniteFourier.quartic_rotation",
    "QuarticFiniteFourier.gaussAmplitude_sq",
    "QuarticFiniteFourier.gaussAmplitude_roots",
    "QuarticFiniteFourier.character_expansion",
    "QuarticFiniteFourier.twisted_gaussian",
    "QuarticFiniteFourier.shiftedDualEquiv",
    "QuarticFiniteFourier.gaussianDualEquiv",
    "QuarticFiniteFourier.shifted_frequency_norm",
    "QuarticFiniteFourier.shifted_frequency_character",
    "QuarticFiniteFourier.gaussian_lattice_transform",
    "QuarticFiniteFourier.quadrantEquiv",
    "QuarticFiniteFourier.reading_rotation",
    "QuarticFiniteFourier.gaussianLattice_four_quarters",
    "QuarticSlope.uniform_sinc_lower",
    "QuarticGrid.checked_curvature_sum",
    "QuarticGrid.checked_slope_sum",
    "QuarticGrid.nonneg_of_grid",
    "QuarticGrid.curvature_of_grid",
    "QuarticGrid.slope_of_grid",
    "QuarticGrid.last_cells_bound",
    "QuarticGrid.encloses_last_cells",
    "QuarticGrid.assemble_from_grid",
    "QuarticGrid.exp_bounds",
    "QuarticGrid.scale_bounds",
    "QuarticGrid.pointwise_from_gap",
    "QuarticGrid.check_pointwise_cell",
    "QuarticGrid.encloses_outer_core",
}
VERIFIED_ANALYTIC = {
    "QuarticKernel.weighted_coefficients",
    "QuarticKernel.shellArray_reads_coeff",
    "QuarticKernel.shellTest_sound",
    "QuarticFixed.expBox_spec",
    "QuarticFixed.expNegBox_spec",
    "QuarticFixed.powBox_spec",
    "QuarticKernel.thetaBox_sound",
    "QuarticKernel.checkCoreCells_sound",
    "QuarticKernel.sinc_global_floor",
    "QuarticKernel.sharp_quantitative_reading",
}
KERNEL_AUDITED = {
    "QuarticKernel.kernelReading_eq",
    "QuarticKernel.annulusStats_final",
    "QuarticKernel.annulusStats_weighted",
    "QuarticKernel.annulusStats_prefix",
    "QuarticKernel.sweepAnnulusStats_eq",
    "QuarticKernel.checkSpans_final",
    "QuarticKernel.checkSpans_weight",
    "QuarticKernel.checkSpans_positive",
    "QuarticKernel.checkSpansStrict_eq",
    "QuarticKernel.KernelBinChain.sound",
    "QuarticKernel.checkCoreCells_of_ranges",
    "QuarticKernel.actual_checked_shells_kernel",
    "QuarticKernel.actual_cells_kernel",
    "QuarticKernel.actual_quartic_certificate_kernel",
    "QuarticKernel.verified_quartic_direction_kernel",
    "QuarticKernel.verified_quartic_zero_on_line_kernel",
}
BAND_AUDITED = {
    "QuarticKernel.bandStats_append",
    "QuarticKernel.annulusStats_band",
    "QuarticKernel.checkSpans_of_annulus",
}


def room_for_lean_worker():
    if os.name != "nt":
        return True
    import ctypes
    from ctypes import wintypes

    class MemoryStatus(ctypes.Structure):
        _fields_ = [("size", wintypes.DWORD), ("load", wintypes.DWORD)] + [
            (field, ctypes.c_ulonglong) for field in ("total_ram", "free_ram", "total_commit", "free_commit",
                                                      "total_virtual", "free_virtual", "free_extended")]

    memory = MemoryStatus()
    memory.size = ctypes.sizeof(memory)
    return (ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(memory))
            and memory.free_ram >= 5 * 2**30 and memory.free_commit >= 7 * 2**30)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    add_lean_options(parser)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--checkpoint", type=Path, default=BUILD / "certificate")
    parser.add_argument("--log", type=Path, default=BUILD / "certificate.log")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    BUILD.mkdir(parents=True, exist_ok=True)
    unpack_generated()
    lean, version, libraries = lean_environment(args.lake_project, args.lean)
    stage = args.checkpoint.resolve()
    stage.mkdir(parents=True, exist_ok=True)
    args.log.parent.mkdir(parents=True, exist_ok=True)
    compiled, reports = {}, {}
    external, reused = {}, set()
    log_lock = Lock()

    def record(message):
        with log_lock:
            print(message, file=log, flush=True)
            print(message, flush=True)

    def run(command, stage, env):
        result = subprocess.run([str(item) for item in command], cwd=stage, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                encoding="utf-8", check=False)
        if result.stdout.strip():
            record(result.stdout.rstrip())
        result.check_returncode()
        return result.stdout

    with ExitStack() as resources:
        guard = resources.enter_context((stage / ".replay.lock").open("a+b"))
        guard.seek(0)
        try:
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(guard.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(guard.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise RuntimeError(f"A replay is already using {stage}") from exc
        log = resources.enter_context(args.log.open("w", encoding="utf-8", newline="\n"))
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [stage, *libraries])),
                   LEAN_NUM_THREADS="2")
        record(version.strip())

        def build(module):
            if module in compiled:
                return compiled[module]
            relative = Path(*module.split(".")).with_suffix(".lean")
            source = next((root / relative for root in SOURCE_ROOTS if (root / relative).is_file()), None)
            if source is None:
                if module in external:
                    return external[module]
                artifact = next((lib / relative.with_suffix(".olean") for lib in libraries
                                 if (lib / relative.with_suffix(".olean")).is_file()), None)
                if artifact is not None:
                    external[module] = hashlib.sha256(artifact.read_bytes()).hexdigest()
                    return external[module]
                raise FileNotFoundError(f"Missing compiled Mathlib dependency {module}")
            contents = source.read_bytes()
            dependencies = re.findall(r"^import\s+(\S+)", contents.decode("utf-8-sig"), re.MULTILINE)
            digest = hashlib.sha256(contents).hexdigest()
            inputs = [version, digest, *(build(dependency) for dependency in dependencies)]
            fingerprint = hashlib.sha256("\n".join(inputs).encode()).hexdigest()
            destination = stage / relative
            artifact = destination.with_suffix(".olean")
            receipt = destination.with_suffix(".verified.json")
            destination.parent.mkdir(parents=True, exist_ok=True)
            output = None
            if receipt.is_file() and artifact.is_file():
                try:
                    previous = json.loads(receipt.read_text(encoding="utf-8"))
                    if (previous["input"] == fingerprint and
                            isinstance(previous["output"], str) and
                            previous["artifact"] == hashlib.sha256(artifact.read_bytes()).hexdigest()):
                        output = previous["output"]
                except (KeyError, json.JSONDecodeError, TypeError):
                    pass
            if output is None:
                destination.write_bytes(contents)
                if module.startswith("KernelNumerics."):
                    record(f"Checking {module}")
                options = ["-j", "1", "-s", "65536"]
                try:
                    output = run([lean, *options, "-DwarningAsError=true", "-o",
                                  relative.with_suffix(".olean"), relative], stage, env)
                except subprocess.CalledProcessError:
                    record(f"Failed {module}  sha256={digest}")
                    raise
                saved = {"input": fingerprint, "artifact": hashlib.sha256(artifact.read_bytes()).hexdigest(),
                         "output": output}
                temporary = receipt.with_suffix(".tmp")
                temporary.write_text(json.dumps(saved, ensure_ascii=False), encoding="utf-8")
                temporary.replace(receipt)
                record(f"Compiled {module}  sha256={digest}")
            else:
                reused.add(module)
                if output.strip():
                    record(output.rstrip())
                record(f"Reused {module}  sha256={digest}")
            for name, axioms in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",
                                           output, re.MULTILINE):
                reports[name] = {item.strip() for item in axioms.split(",") if item.strip()}
            for name in re.findall(r"^'([^']+)' does not depend on any axioms", output, re.MULTILINE):
                reports[name] = set()
            compiled[module] = fingerprint
            return fingerprint

        def build_blocks(folder):
            sources = sorted((GENERATED / folder).glob("Block*.lean"),
                             key=lambda source: int(source.stem.removeprefix("Block")))
            pending = deque(f"{folder}.{source.stem}" for source in sources)
            limit = args.jobs
            next_start = 0.0
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                jobs = {}
                try:
                    while pending or jobs:
                        while pending and len(jobs) < limit:
                            module = pending[0]
                            relative = stage.joinpath(*module.split("."))
                            saved = (relative.with_suffix(".verified.json").is_file()
                                     and relative.with_suffix(".olean").is_file())
                            if jobs and not saved and (time.monotonic() < next_start or not room_for_lean_worker()):
                                break
                            pending.popleft()
                            if not saved:
                                next_start = time.monotonic() + 12
                                record(f"Checking {module} [{len(jobs)+1} active of up to {limit} Lean workers].")
                            jobs[pool.submit(build, module)] = (module, limit)
                        poll = 5 if pending and len(jobs) < limit else None
                        done, _ = wait(jobs, timeout=poll, return_when=FIRST_COMPLETED)
                        for job in done:
                            module, submitted_limit = jobs.pop(job)
                            try:
                                job.result()
                            except subprocess.CalledProcessError as exc:
                                diagnostic = (exc.output or "").lower()
                                if submitted_limit == 1 or not any(
                                    phrase in diagnostic for phrase in ("bad_alloc", "out of memory")
                                ):
                                    raise
                                limit = min(limit, submitted_limit - 1)
                                record(f"Retrying {module} after a memory failure with at most {limit} Lean workers.")
                                pending.appendleft(module)
                except BaseException:
                    for job in jobs:
                        job.cancel()
                    raise

        build("QuarticKernelStrict")
        build("QuarticAnnulusAssembly")
        build_blocks("KernelPrefixes")
        build("QuarticCheckedShellKernel")
        build("QuarticCellChecker")
        build_blocks("KernelCells")
        build("QuarticVerifiedKernel")
        audited = AUDITED | VERIFIED_ANALYTIC | KERNEL_AUDITED | BAND_AUDITED
        build("QuarticMellinContinuation")
        build("QuarticDirectSign")
        if missing := audited - reports.keys():
            raise ValueError(f"Missing #print axioms output for {sorted(missing)}")
        for name in sorted(audited):
            if extra := reports[name] - AXIOMS:
                raise ValueError(f"{name} uses extra axioms: {sorted(extra)}")
        if reused:
            record(f"Resumed source build passed. {len(compiled) - len(reused)} project modules compiled and "
                   f"{len(reused)} verified artifacts reused.")
        else:
            record(f"Clean source build passed. {len(compiled)} project modules compiled.")
        record("All named lemmas passed the axiom audit.")
        record(KERNEL_PASS)


if __name__ == "__main__":
    main()
