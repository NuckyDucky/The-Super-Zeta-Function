"""Write the independent Lean kernel checks for the enclosure table."""

from pathlib import Path


ROOT = Path(__file__).resolve().parent
COUNT = 1051
WIDTH = 16


def main():
    blocks = ROOT / "KernelCells"
    blocks.mkdir(exist_ok=True)
    names = []
    for first in range(0, COUNT, WIDTH):
        block = first // WIDTH
        name = f"Block{block:02}"
        names.append(name)
        size = min(WIDTH, COUNT - first)
        lines = [
            "import QuarticCellChecker",
            "",
            "namespace QuarticKernel.KernelCells",
            "",
            "set_option maxRecDepth 18000",
            "set_option maxHeartbeats 4000000",
            "",
        ]
        expression = f"checkCoreCellRange_succ {first} 0 rfl cell{first}"
        for n in range(first, first + size):
            lines += [
                f"private theorem cell{n} : checkCoreCellRange {n} 1 = true := by",
                "  decide +kernel",
                "",
            ]
            if n > first:
                expression = f"checkCoreCellRange_succ {first} {n-first} ({expression}) cell{n}"
        lines += [
            f"theorem block{block} : checkCoreCellRange {first} {size} = true :=",
            f"  {expression}",
            "",
            f"#print axioms block{block}",
            "",
            "end QuarticKernel.KernelCells",
            "",
        ]
        (blocks / f"{name}.lean").write_text("\n".join(lines), encoding="utf-8")

    lines = [*(f"import KernelCells.{name}" for name in names), "",
             "namespace QuarticKernel", "",
             "theorem actual_cells_kernel : checkCoreCells = true := by",
             "  apply checkCoreCells_of_ranges",
             "  intro k hk",
             "  interval_cases k"]
    lines += [f"  · exact KernelCells.block{k}" for k in range(len(names))]
    lines += ["", "#print axioms actual_cells_kernel", "", "end QuarticKernel", ""]
    (ROOT / "QuarticCheckedCellsKernel.lean").write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
