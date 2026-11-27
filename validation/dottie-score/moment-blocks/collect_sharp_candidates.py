"""Read the sharp-score checkpoints and assemble their integer candidate in Lean."""

import argparse
import json
import re
from pathlib import Path

from replay_sharp_candidates import COLUMNS, CUTOFF, ROW_COUNT, check_row


def scan_checkpoint(path, first, stop, digest):
    header = f"# dottie-sharp-v1 {CUTOFF} {COLUMNS} {first} {stop} {digest}\n".encode()
    totals = [0] * COLUMNS
    expected = first
    try:
        stream = path.open("rb")
    except FileNotFoundError:
        return expected, totals
    with stream:
        initial = stream.readline()
        if not initial.endswith(b"\n") and header.startswith(initial):
            return expected, totals
        if initial != header:
            raise ValueError(f"Invalid checkpoint header in {path.name}")
        for record in stream:
            if not record.endswith(b"\n"):
                break
            if expected >= stop:
                raise ValueError(f"Extra row in {path.name}")
            check_row(record, expected)
            for column, value in enumerate(record.split(b"\t")[1:]):
                totals[column] += int(value)
            expected += 1
    return expected, totals


def collect(plan_path):
    plan = json.loads(plan_path.read_text(encoding="utf-8-sig"))
    if (plan["cutoff"], plan["columns"], plan["rows"]) != (CUTOFF, COLUMNS, ROW_COUNT):
        raise ValueError("Run plan does not match the pinned sharp cutoff and row shape")
    digest = plan["inputs_sha256"]["DottieSharpCandidateMain.lean"]
    if not re.fullmatch("[a-f0-9]{64}", digest):
        raise ValueError("Invalid Lean entry point hash in the run plan")

    totals = [0] * COLUMNS
    completed = 0
    next_start = 0
    for shard in plan["ranges"]:
        first, stop = shard["first"], shard["stop"]
        if first != next_start or not first < stop <= ROW_COUNT:
            raise ValueError("Checkpoint ranges must partition the prefix in order")
        filename = f"rows-{first}-{stop}.tsv"
        if shard["checkpoint"] != filename:
            raise ValueError(f"Expected checkpoint name {filename}")
        expected, subtotal = scan_checkpoint(plan_path.parent / filename, first, stop, digest)
        completed += expected - first
        totals = [total + addend for total, addend in zip(totals, subtotal)]
        print(f"Rows [{first}, {stop}): {expected - first:,} / {stop - first:,}")
        next_start = stop
    if next_start != ROW_COUNT:
        raise ValueError("Checkpoint ranges do not reach the last prefix row")
    return completed, totals


def lean_candidate(totals):
    pairs = ",\n".join(f"  ({real}, {imag})" for real, imag in zip(totals[::2], totals[1::2]))
    return f"""import DottieDirectJointMomentSpans

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000

/-- Candidate totals from the compiled row evaluator. -/
def dottieFullSharpCandidateTicks : List (ℤ × ℤ) := [
{pairs}]

theorem dottie_full_sharp_candidate_fits :
    dottieSharpScoresFit dottieFullSharpCandidateTicks = true := by
  decide +kernel

/-- Using these totals on the circle still requires the exact span equality. -/
theorem dottie_sharp_margin_of_candidate_eq
    (hValue : dottieDirectJointMomentSpan 11 dottiePrefixEnd 0 dottiePrefixEnd.sqrt =
      dottieFullSharpCandidateTicks)
    (hReference : dottieRelativeReferenceProjection ≤ 171687/10^6) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) :=
  dottie_sharp_margin_of_direct_span _ hValue dottie_full_sharp_candidate_fits hReference

#print axioms dottie_full_sharp_candidate_fits
#print axioms dottie_sharp_margin_of_candidate_eq

end QuarticModel.DottieFixedIntervals
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plan", type=Path)
    parser.add_argument("--lean-output", type=Path, help="write a new Lean file once every row is present")
    args = parser.parse_args()
    try:
        completed, totals = collect(args.plan)
        print(f"Total: {completed:,} / {ROW_COUNT:,} rows")
        if args.lean_output is not None:
            if completed != ROW_COUNT:
                raise ValueError("Candidate output requires all checkpoint rows")
            with args.lean_output.open("x", encoding="utf-8", newline="\n") as stream:
                stream.write(lean_candidate(totals))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
