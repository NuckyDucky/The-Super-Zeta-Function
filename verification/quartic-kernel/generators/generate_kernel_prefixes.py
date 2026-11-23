"""Generate checkpoint witnesses for independent Lean kernel checks."""

import argparse
from math import isqrt
from pathlib import Path
import re
import sys

import numpy as np


ROOT = Path(__file__).resolve().parent
CUTOFF = 2**25
CHUNK = 2**20
BLOCK_SIZE = 32
BLOCK_NORMS = 2**18


def point_counts(lo, hi):
    """Unsigned quarter-lattice shell counts used to choose span widths."""
    counts = np.zeros(hi - lo, dtype=np.int64)
    for a in range(1, isqrt(hi) + 1):
        square = a*a
        first = isqrt(lo - square) + 1 if lo >= square else 0
        stop = isqrt(hi - square) + 1
        b = np.arange(first, stop, dtype=np.int64)
        counts[square + b*b - lo - 1] += 1
    return counts


def plan_spans(first, stop, prefix, unsigned):
    widths = []
    while first < stop:
        target = int(unsigned[first] + prefix[first] - 1)
        end = int(np.searchsorted(unsigned, target, side="right")) - 1
        end = min(stop, max(first + 1, end))
        widths.append(end - first)
        first = end
    return widths


def witnesses(repo):
    sys.path.insert(0, str(repo / "tools"))
    from gaussian_moments import signed_counts

    source = (ROOT / "QuarticShellBins.lean").read_text(encoding="utf-8")
    bins = [tuple(map(int, match)) for match in re.findall(r"⟨(\d+), (\d+)⟩", source)]
    bins.append((1, 17505))
    if sum(width for width, _ in bins) != CUTOFF:
        raise ValueError("The signed-prefix table must cover exactly the certificate cutoff.")
    i = 0
    state = 0
    for lo in range(0, CUTOFF, CHUNK):
        hi = lo + CHUNK
        counts = signed_counts(lo, hi)
        prefix = np.concatenate(([state], state + counts.cumsum(dtype=np.int64)))
        points = np.concatenate(([0], point_counts(lo, hi).cumsum()))
        j = 0
        while j < CHUNK:
            width, mass = bins[i]
            end = j + width
            if end > CHUNK or mass != int(prefix[j+1:end+1].sum()):
                raise ValueError(f"The stored bin {i} disagrees with the checkpoint generator.")
            spans = plan_spans(j, end, prefix, points)
            yield lo + j, int(prefix[j]), width, mass, int(prefix[end]), spans
            j = end
            i += 1
        state = int(prefix[-1])
    if i != len(bins) or state != 17505:
        raise ValueError("The final generated checkpoint does not match the certificate.")


def write_block(directory, index, rows):
    name = f"Block{index:02}"
    first = rows[0]
    end = rows[-1][4]
    lines = [
        "import QuarticKernelStrict",
        "",
        "namespace QuarticKernel.KernelPrefixes",
        "",
        "set_option maxRecDepth 24000",
        "set_option maxHeartbeats 0",
        "",
    ]
    for j, (lo, initial, width, weight, final, spans) in enumerate(rows):
        tag = f"{index}_{j}"
        lines += [
            f"private def widths{tag} : List ℕ := [{', '.join(map(str, spans))}]",
            f"private theorem size{tag} : spanWidth widths{tag} = {width} := by decide",
            f"private theorem eval{tag} : checkSpansStrict {lo} {initial} widths{tag} = "
            f"({final}, {weight}, true) := by decide +kernel",
            f"private theorem check{tag} : checkSpans {lo} {initial} widths{tag} = "
            f"({final}, {weight}, true) := by",
            f"  simpa only [checkSpansStrict_eq] using eval{tag}",
            "",
        ]
    bins = ", ".join(f"⟨{width}, {mass}⟩" for _, _, width, mass, _, _ in rows)
    lines += [
        f"def bins{index} : List ShellBin := [{bins}]",
        f"theorem block{index} : KernelBinChain {first[0]} {first[1]} bins{index} {end} := by",
        f"  unfold bins{index}",
    ]
    lines.extend(f"  apply KernelBinChain.cons widths{index}_{j} (by decide) size{index}_{j} check{index}_{j}"
                 for j in range(len(rows)))
    lines += ["  exact KernelBinChain.nil _ _", "", f"#print axioms block{index}",
              "", "end QuarticKernel.KernelPrefixes", ""]
    (directory / f"{name}.lean").write_text("\n".join(lines), encoding="utf-8")
    return name, first[0], first[1], end


def write_assembly(blocks):
    lines = [*(f"import KernelPrefixes.{name}" for name, *_ in blocks),
             "import QuarticShellBins", "", "namespace QuarticKernel", "",
             "set_option maxRecDepth 24000", "set_option maxHeartbeats 2000000", ""]

    def assemble(first, last):
        if first == last:
            return f"KernelPrefixes.bins{first}", f"KernelPrefixes.block{first}"
        middle = (first + last) // 2
        left_bins, left_proof = assemble(first, middle)
        right_bins, right_proof = assemble(middle + 1, last)
        _, start, initial, _ = blocks[first]
        _, _, _, final = blocks[last]
        bins = f"bins_{first}_{last}"
        proof = f"checked_chain_{first}_{last}"
        lines.extend([
            f"private def {bins} : List ShellBin := {left_bins} ++ {right_bins}",
            f"private theorem {proof} : KernelBinChain {start} {initial} {bins} {final} :=",
            f"  KernelBinChain.append {left_proof} {right_proof}", "",
        ])
        return bins, proof

    bins, checked = assemble(0, len(blocks) - 1)
    lines += [f"private def checkedBins : List ShellBin := {bins}",
             "private theorem bins_eq : checkedBins = actualBins ++ [⟨1,17505⟩] := rfl",
             "private theorem bin_count : binCount checkedBins = 33554432 := by decide",
             "",
             "private theorem checked_chain : KernelBinChain 0 0 checkedBins 17505 :=",
             f"  {checked}", "",
              "private theorem bins_left {i : ℕ} (xs ys : List ShellBin)",
              "    (h : BinsCorrect i (xs++ys)) : BinsCorrect i xs := by",
              "  induction xs generalizing i with",
              "  | nil => trivial",
              "  | cons g gs ih => exact ⟨h.1,h.2.1,ih h.2.2⟩",
              "",
              "theorem actual_checked_shells_kernel :",
              "    (∀ j : ℕ, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) ∧",
              "      BinsCorrect 0 actualBins ∧ prefixSum 33554432 = 17505 := by",
              "  obtain ⟨hb,hf,hp⟩ := checked_chain.sound (by simp [prefixSum])",
              "  rw [bins_eq] at hb",
              "  rw [bin_count,Nat.zero_add] at hf hp",
              "  exact ⟨hp,bins_left actualBins [⟨1,17505⟩] hb,hf⟩",
              "", "#print axioms actual_checked_shells_kernel", "", "end QuarticKernel", ""]
    (ROOT / "QuarticCheckedShellKernel.lean").write_text("\n".join(lines), encoding="utf-8")


def partition(rows):
    block = []
    width = 0
    for row in rows:
        row_width = row[2]
        if block and (len(block) >= BLOCK_SIZE or width + row_width > BLOCK_NORMS):
            yield block
            block = []
            width = 0
        block.append(row)
        width += row_width
    if block:
        yield block


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    args = parser.parse_args()
    directory = ROOT / "KernelPrefixes"
    directory.mkdir(exist_ok=True)
    blocks = [write_block(directory, i, block)
              for i, block in enumerate(partition(witnesses(args.project)))]
    write_assembly(blocks)


if __name__ == "__main__":
    main()
