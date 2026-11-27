"""Assemble consecutive Lean row certificates under the original Dottie weight."""

import argparse
import re
from pathlib import Path

from generate_fast_reference_replay import CUTOFF, FAST_WEIGHT, ROW_COUNT, Span, render_span


MODULE = re.compile(r"DottieFastReferenceRows(\d+)To(\d+)")
ORIGINAL_WEIGHT = "dottieDirectReferenceWeight"


def read_span(path):
    match = MODULE.fullmatch(path.stem)
    if match is None:
        raise ValueError(f"Expected a generated row certificate, received {path}")
    first, stop = map(int, match.groups())
    if not 0 <= first < stop <= ROW_COUNT:
        raise ValueError(f"Invalid range in {path}")
    theorem = f"dottieFastReferenceRows{first}To{stop}"
    proof = path.read_text(encoding="utf-8-sig")
    decl = re.compile(
        rf"(?m)^theorem {theorem} :\s+"
        rf"dottiePairedRowSpan {CUTOFF} {FAST_WEIGHT} {first} {stop-first} = "
        r"\((-?\d+) : ℤ\) :="
    )
    values = decl.findall(proof)
    if len(values) != 1:
        raise ValueError(f"Expected one matching declaration in {path}")
    return Span(first, stop, theorem, int(values[0]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("sources", type=Path, nargs="+")
    args = parser.parse_args()
    inputs = sorted((read_span(path), path.stem) for path in args.sources)
    for (left, _), (right, _) in zip(inputs, inputs[1:]):
        if left.stop != right.first:
            parser.error(f"The spans overlap or leave a gap at row {left.stop}")
    lines = [f"import {module}" for _, module in inputs]
    lines.extend(["", "namespace QuarticModel", ""])
    first, stop, source, total = render_span(lines, [span for span, _ in inputs])
    suffix = f"Prefix{stop}" if first == 0 else f"Span{first}To{stop}"
    name = f"dottieDirectReference{suffix}"
    lines.extend([
        f"theorem {name} :",
        f"    dottiePairedRowSpan {CUTOFF} {ORIGINAL_WEIGHT} {first} {stop-first} = ({total} : ℤ) := by",
        f"  simpa only [funext dottie_fast_reference_weight_eq] using {source}",
        "",
        f"#print axioms {name}",
        "",
    ])
    if first == 0 and stop == ROW_COUNT:
        lines.extend([
            "theorem dottie_direct_reference_score_eq_replayed :",
            f"    dottieDirectReferenceScore = ({total} : ℤ) := by",
            "  unfold dottieDirectReferenceScore",
            f"  rw [show ({CUTOFF} : ℕ).sqrt = {ROW_COUNT} by decide +kernel]",
            f"  exact {name}",
            "",
            "#print axioms dottie_direct_reference_score_eq_replayed",
            "",
        ])
    lines.extend(["end QuarticModel", ""])
    args.output.mkdir(parents=True, exist_ok=True)
    path = args.output / f"DottieFastReference{suffix}.lean"
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write("\n".join(lines))
    print(f"{path} {stop-first} rows total {total}")


if __name__ == "__main__":
    main()
