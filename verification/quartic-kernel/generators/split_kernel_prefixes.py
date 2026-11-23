"""Replace long prefix reductions with kernel-checked row bands."""
import argparse
from functools import cache
from math import isqrt
from pathlib import Path
import re

import numpy as np


CONDUCTOR = ((41, 32), (457, 109), (1414835497, 516876951))
EVALUATION = re.compile(
    r"^private theorem eval(?P<tag>\d+_\d+) : checkSpansStrict (?P<lo>\d+) (?P<initial>-?\d+) "
    r"widths(?P=tag) = \((?P<final>-?\d+), (?P<mass>-?\d+), true\) := by decide \+kernel\n"
    r"private theorem check(?P=tag) : [^\n]+\n"
    r"  simpa only \[checkSpansStrict_eq\] using eval(?P=tag)$",
    re.M,
)


@cache
def residue_table(prime):
    return np.array([pow(r, (prime - 1) // 2, prime) for r in range(prime)], dtype=np.int64)


def band_data(lo, hi, max_points):
    rows = np.arange(1, isqrt(hi) + 1, dtype=np.int64)
    first = np.fromiter((isqrt(lo - a*a) + 1 if lo >= a*a else 0 for a in range(1, len(rows)+1)),
                        dtype=np.int64, count=len(rows))
    after = np.fromiter((isqrt(hi - a*a) + 1 for a in range(1, len(rows)+1)),
                        dtype=np.int64, count=len(rows))
    sizes = after - first
    offsets = np.concatenate(([0], sizes.cumsum()))
    a = np.repeat(rows, sizes)
    b = np.arange(len(a), dtype=np.int64) + np.repeat(first - offsets[:-1], sizes)
    norms = a*a + b*b
    marks = np.ones(len(a), dtype=np.int64)
    for prime, root in CONDUCTOR:
        residues = (a + root*b) % prime
        if prime < 1024:
            values = residue_table(prime)[residues]
        else:
            assert prime*prime < 2**63
            exponent = (prime - 1) // 2
            values = np.ones(len(a), dtype=np.int64)
            while exponent:
                if exponent & 1:
                    values = values * residues % prime
                residues = residues * residues % prime
                exponent //= 2
        marks *= np.where(values == prime-1, -1, values)
    totals = np.stack((marks, marks*(hi+1-norms), np.minimum(marks, 0)))
    sums = np.column_stack((np.zeros(3, dtype=np.int64), totals.cumsum(axis=1)))
    start = 0
    while start < len(rows):
        limit = int(np.searchsorted(offsets, offsets[start]+max_points, side="right")) - 1
        end = min(len(rows), max(start+1, limit))
        yield start, end-start, tuple(map(int, sums[:, offsets[end]] - sums[:, offsets[start]]))
        start = end


def as_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def stats_tuple(values):
    return "(" + ", ".join(map(str, values)) + ")"


def prove_annulus(lines, stem, lo, hi, max_points):
    bands = list(band_data(lo, hi, max_points))
    for index, (start, count, stats) in enumerate(bands):
        lines.append(f"private theorem {stem}_band{index} : bandStats {lo} {hi} {start} {count} ="
                     f" {stats_tuple(stats)} := by decide +kernel")

    def merge(left, right):
        if left == right:
            start, count, stats = bands[left]
            return f"{stem}_band{left}", start, count, stats
        middle = (left + right)//2
        left_name, start, left_count, a = merge(left, middle)
        right_name, _, right_count, b = merge(middle+1, right)
        name = f"{stem}_sum{left}_{right}"
        count = left_count + right_count
        stats = tuple(x+y for x,y in zip(a,b))
        lines.extend([
            f"private theorem {name} : bandStats {lo} {hi} {start} {count} = {stats_tuple(stats)} := by",
            f"  have joined := bandStats_append {lo} {hi} {start} {left_count} {right_count}",
            f"  rw [{left_name}, {right_name}] at joined",
            "  exact joined",
        ])
        return name, start, count, stats

    joined, _, rows, stats = merge(0, len(bands)-1)
    lines.extend([
        f"private theorem {stem}_stats : annulusStats {lo} {hi} = {stats_tuple(stats)} := by",
        f"  rw [annulusStats_band, show annulusRowCount {hi} = {rows} by decide +kernel]",
        f"  exact {joined}",
    ])
    return stats


def prove_bin(match, contents, max_points):
    tag = match["tag"]
    declared = re.search(r"^private def widths" + tag + r" : List ℕ := \[([^\]]+)\]$", contents, re.M)
    widths = [int(w) for w in declared.group(1).split(", ")]
    i = int(match["lo"])
    s = int(match["initial"])
    spans = []
    lines = []
    for k, w in enumerate(widths):
        stem = f"a{tag}_{k}"
        count, mass, negative = prove_annulus(lines, stem, i, i+w, max_points)
        assert s + (count if w == 1 else negative) >= 1, (tag, k, s, count, negative)
        spans.append((i, s, w, w*s+mass, stem))
        i += w
        s += count
    assert s == int(match["final"]) and sum(span[3] for span in spans) == int(match["mass"]), tag
    lines.append(f"private theorem tail{tag}_{len(spans)} : checkSpans {i} {s} [] = ({s}, 0, true) := rfl")
    accumulated = 0
    for k in reversed(range(len(spans))):
        lo, initial, width, mass, stem = spans[k]
        accumulated += mass
        lines.extend([
            f"private theorem tail{tag}_{k} : checkSpans {lo} {initial} {as_list(widths[k:])} = ({s}, {accumulated}, true) :=",
            f"  checkSpans_of_annulus (i := {lo}) (w := {width}) (s := {initial}) (ws := {as_list(widths[k+1:])})",
            f"    {stem}_stats (by decide) tail{tag}_{k+1}",
        ])
    lines.extend([
        f"private theorem check{tag} : checkSpans {match['lo']} {match['initial']} widths{tag} =",
        f"    ({match['final']}, {match['mass']}, true) := tail{tag}_0",
    ])
    return "\n".join(lines)


def rewrite_block(contents, max_points, probe=False):
    matches = list(EVALUATION.finditer(contents))
    if not matches:
        raise ValueError("No strict kernel reductions found")
    contents = contents.replace("import QuarticKernelStrict", "import QuarticAnnulusBands", 1)
    if probe:
        first = EVALUATION.search(contents)
        tag = first["tag"]
        prefix = contents[:first.start()]
        return (prefix + prove_bin(first, contents, max_points) +
                f"\n#print axioms check{tag}\nend QuarticKernel.KernelPrefixes\n")
    return EVALUATION.sub(lambda match: prove_bin(match, contents, max_points), contents)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--points", type=int, default=1024)
    parser.add_argument("--probe", action="store_true")
    args = parser.parse_args()
    if args.points <= 0:
        parser.error("--points must be positive")
    src = args.source.read_text(encoding="utf-8-sig")
    args.destination.write_text(rewrite_block(src, args.points, args.probe), encoding="utf-8")


if __name__ == "__main__":
    main()
