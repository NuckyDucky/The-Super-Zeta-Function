"""Generate one Lean certificate for a consecutive range of Dottie reference rows."""

import argparse
import re
from math import isqrt
from pathlib import Path
from typing import NamedTuple

from replay_direct_reference_candidates import CUTOFF, ROW_COUNT, paired_block, row_sign, weight


WIDTH = 1024
PACKED_BLOCK = re.compile(
    r"dottiePairRowBlock dottieQuickWeightTicks (\d+) (\d+) (\d+) =\s*"
    r"\(-?\d+ : ℤ\) :=\s*dottie_pair_block_of_packed_witness "
    r"\(packed := (0x[0-9a-fA-F]+)\)"
)
FAST_WEIGHT = "dottieFastReferenceWeight"


class Span(NamedTuple):
    first: int
    stop: int
    theorem: str
    total: int


def row_head(row, limit):
    a = row + 1
    square = a * a
    axis = row_sign(a, 0) * weight(square)
    diagonal = row_sign(a, a) * weight(2 * square) if row < limit else 0
    return axis + diagonal


def archived_witnesses(witness_root, first, stop):
    if witness_root is None:
        return {}
    witnesses = {}
    for pattern in ("DottiePairedRow*.lean", "*/kernel/DottiePairedRow*.lean"):
        for path in witness_root.glob(pattern):
            match = re.fullmatch(r"DottiePairedRow(?:(\d+)|s(\d+)Through(\d+))", path.stem)
            if match is None:
                continue
            archive_first = int(match[1] or match[2]) - 1
            archive_stop = int(match[1] or match[3])
            if archive_stop <= first or stop <= archive_first:
                continue
            for block in PACKED_BLOCK.finditer(path.read_text(encoding="utf-8-sig")):
                row, lo, length = map(int, block.groups()[:3])
                if not archive_first <= row < archive_stop:
                    raise ValueError(f"Packed row outside the declared range in {path}")
                if first <= row < stop:
                    row_blocks = witnesses.setdefault(row, {})
                    if (lo, length) in row_blocks:
                        raise ValueError(f"Duplicate archived block for row {row} in {path}")
                    row_blocks[lo, length] = block[4]
    return witnesses


def read_checkpoints(paths, first, stop):
    totals = {}
    for path in paths:
        with path.open(encoding="ascii") as stream:
            for line in stream:
                if not line.endswith("\n"):
                    raise ValueError(f"Incomplete checkpoint record in {path}")
                row, total = map(int, line.split())
                if first <= row < stop:
                    if row in totals:
                        raise ValueError(f"Duplicate checkpoint row {row}")
                    totals[row] = total
    if paths and len(totals) != stop - first:
        raise ValueError("The checkpoints must include every selected row")
    return totals


def render_row(lines, row, witnesses):
    limit = isqrt(CUTOFF - (row + 1) ** 2)
    full, tail = divmod(min(row, limit), WIDTH)
    blocks = [(part * WIDTH, WIDTH) for part in range(full)] + [(full * WIDTH, tail)]
    if witnesses and set(witnesses) != {block for block in blocks if block[1]}:
        raise ValueError(f"Packed witness ranges do not match row {row}")
    head = row_head(row, limit)
    head_name = f"row{row}_head"
    row_name = f"row{row}"
    lines.extend([
        f"private theorem {head_name} : dottiePairRowHead {CUTOFF} {FAST_WEIGHT} {row} =",
        f"    ({head} : ℤ) := by decide +kernel",
        "",
    ])
    total = head
    names = []
    for lo, count in blocks:
        name = f"row{row}_block{lo}"
        ticks = paired_block(row, lo, count)
        names.append(name)
        total += ticks
        lines.extend([
            f"private theorem {name} : dottiePairRowBlock {FAST_WEIGHT} {row} {lo} {count} =",
            f"    ({ticks} : ℤ) :=",
        ])
        if not count:
            lines.append("  by decide +kernel")
        elif witnesses:
            lines.extend([
                f"  dottie_pair_block_of_packed_witness (packed := {witnesses[lo, count]})",
                "    (by decide +kernel)",
            ])
        else:
            lines.extend([
                "  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq",
                f"    {FAST_WEIGHT} {row} {lo} {count}).symm.trans (by decide +kernel)",
            ])
        lines.append("")
    lines.extend([
        f"private theorem {row_name} :",
        f"    dottiePairedRowSpan {CUTOFF} {FAST_WEIGHT} {row} 1 = ({total} : ℤ) := by",
        f"  rw [dottiePairedRowSpan_one, {head_name}, dottiePairRowBlock_eq_blocks _ _ _ {WIDTH}]",
        f"  rw [show dottiePairRowSize {CUTOFF} {row} / {WIDTH} = {full} by decide +kernel,",
        f"    show dottiePairRowSize {CUTOFF} {row} % {WIDTH} = {tail} by decide +kernel]",
    ])
    simp_lemmas = ["Finset.sum_range_zero", "Nat.zero_mul"]
    if full:
        simp_lemmas.extend(["Finset.sum_range_succ", "Nat.reduceMul"])
    lines.extend([
        f"  simp only [{', '.join(simp_lemmas)},",
        f"    {', '.join(names)}]",
        "  decide +kernel",
        "",
    ])
    return Span(row, row + 1, row_name, total)


def render_span(lines, spans):
    if len(spans) == 1:
        return spans[0]
    half = len(spans) // 2
    first, middle, left_name, left = render_span(lines, spans[:half])
    right_start, stop, right_name, right = render_span(lines, spans[half:])
    if middle != right_start:
        raise ValueError(f"Nonconsecutive spans at rows {middle} and {right_start}")
    name = f"span{first}_{stop}"
    total = left + right
    lines.extend([
        f"private theorem {name} :",
        f"    dottiePairedRowSpan {CUTOFF} {FAST_WEIGHT} {first} {stop-first} = ({total} : ℤ) := by",
        "  calc",
        f"    _ = ({left} : ℤ) + ({right} : ℤ) := by",
        f"      simpa only [Nat.reduceAdd, {left_name}, {right_name}] using",
        f"        dottiePairedRowSpan_add {CUTOFF} {FAST_WEIGHT} {first} {middle-first} {stop-middle}",
        "    _ = _ := by decide +kernel",
        "",
    ])
    return Span(first, stop, name, total)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first", type=int)
    parser.add_argument("stop", type=int)
    parser.add_argument("output", type=Path)
    parser.add_argument("--witness-root", type=Path)
    parser.add_argument("--checkpoint", type=Path, action="append", default=[])
    args = parser.parse_args()
    first, stop = args.first, args.stop
    if not 0 <= first < stop <= ROW_COUNT:
        parser.error("Expected a nonempty range of zero-based rows. The stop is exclusive.")
    if args.witness_root is not None and not args.witness_root.is_dir():
        parser.error("Expected a directory of archived row witnesses")
    witnesses = archived_witnesses(args.witness_root, first, stop)
    expected = read_checkpoints(args.checkpoint, first, stop)
    lines = [
        "import DottieFastReferenceScore",
        "import DottieWitnessPairBlocks",
        "",
        "namespace QuarticModel",
        "",
        "set_option maxHeartbeats 30000000",
        "set_option maxRecDepth 12000",
        "",
    ]
    rows = []
    for row in range(first, stop):
        span = render_row(lines, row, witnesses.get(row, {}))
        if expected and span.total != expected[row]:
            raise ValueError(f"Calculated ticks differ from the saved candidate for row {row}")
        rows.append(span)
    _, _, span, total = render_span(lines, rows)
    name = f"dottieFastReferenceRows{first}To{stop}"
    lines.extend([
        f"theorem {name} :",
        f"    dottiePairedRowSpan {CUTOFF} {FAST_WEIGHT} {first} {stop-first} = ({total} : ℤ) :=",
        f"  {span}",
        "",
        f"#print axioms {name}",
        "",
        "end QuarticModel",
        "",
    ])
    args.output.mkdir(parents=True, exist_ok=True)
    path = args.output / f"DottieFastReferenceRows{first}To{stop}.lean"
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write("\n".join(lines))
    print(f"{path} {stop-first} rows {len(witnesses)} with packed witnesses total {total}")


if __name__ == "__main__":
    main()
