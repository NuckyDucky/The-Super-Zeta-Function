"""Generate the Lean inputs for the fixed Dottie Mellin quadrature."""

from argparse import ArgumentParser
from hashlib import sha256
from math import lcm
from pathlib import Path

from flint import acb, arb, ctx

from check_native_mellin_quadrature import (
    NUMERATORS, UNIFORM_NODE_DENOMINATOR, interpolation_weights,
    kernel_value, rounded_sample,
)


def block_payload(block, integer_weights):
    columns = [[] for _ in NUMERATORS]
    column_sums = [[0] * 8 for _ in NUMERATORS]
    for panel in range(64 * block, 64 * (block + 1)):
        for j, node in enumerate(NUMERATORS):
            coordinate = 8192 * panel - 16773120 + node
            value = kernel_value(acb(arb(coordinate) / UNIFORM_NODE_DENOMINATOR))
            row = rounded_sample(value.real), rounded_sample(value.imag)
            columns[j].append(row)
            for side, sample in enumerate(row):
                term = sample
                for k in range(4):
                    column_sums[j][4 * side + k] += term
                    term *= -2 * coordinate
    totals = [
        sum(weight * sums[index] for weight, sums in zip(integer_weights, column_sums))
        for index in range(8)
    ]
    return columns, column_sums, totals


def array_literal(values):
    return "#[" + ", ".join(str(value) for value in values) + "]"


def write_block(directory, block, columns, column_sums, totals):
    name = f"MellinIntegerBlock{block:02d}"
    lines = [
        "import MellinIntegerArithmetic", "",
        f"namespace DottieOriented.NativeSpectrum.MellinInteger.{name}", "",
    ]
    for j, (column, sums) in enumerate(zip(columns, column_sums)):
        lines.append(f"private def column{j:02d} : Column := [")
        for start in range(0, len(column), 4):
            suffix = "," if start + 4 < len(column) else "]"
            lines.append("  " + ", ".join(str(row) for row in column[start:start+4]) + suffix)
        lines += [
            f"private def sum{j:02d} : Array Int := {array_literal(sums)}", "",
            "set_option maxRecDepth 2048 in",
            "set_option maxHeartbeats 2000000 in",
            f"private theorem arithmetic{j:02d} : checkedColumn column{j:02d} sum{j:02d} {block} {j} = true := by",
            "  decide +kernel", "",
        ]
    lines += ["def columns : Block"]
    lines += [f"  | {j} => column{j:02d}" for j in range(len(columns))]
    lines += ["  | _ => []", "", "def columnSums : Nat → Array Int"]
    lines += [f"  | {j} => sum{j:02d}" for j in range(len(columns))]
    lines += ["  | _ => #[]", "", f"def totals : Array Int := {array_literal(totals)}", ""]
    lines += [
        "theorem column_arithmetic (j : Nat) (hj : j < 25) :",
        f"    checkedColumn (columns j) (columnSums j) {block} j = true :=",
        "  match j, hj with",
    ]
    lines += [f"  | {j}, _ => arithmetic{j:02d}" for j in range(len(columns))]
    lines += [
        "  | j+25, h => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 25 j) h)", "",
    ]
    lines += [
        "set_option maxRecDepth 2048 in", "set_option maxHeartbeats 2000000 in",
        "theorem block_arithmetic : checkedBlockTotals columnSums totals = true := by",
        "  decide +kernel", "",
        "#print axioms column_arithmetic", "#print axioms block_arithmetic", "",
        f"end DottieOriented.NativeSpectrum.MellinInteger.{name}", "",
    ]
    encoded = "\n".join(lines).encode("utf-8")
    (directory / f"{name}.lean").write_bytes(encoded)
    return sha256(encoded).hexdigest()


def write_table(directory):
    modules = [f"MellinIntegerBlock{block:02d}" for block in range(37)]
    lines = [f"import {name}" for name in modules]
    lines += ["", "namespace DottieOriented.NativeSpectrum.MellinInteger", ""]
    for name, value_type, member, fallback in (
        ("fixedColumns", "Block", "columns", "fun _ => []"),
        ("fixedColumnSums", "Nat → Array Int", "columnSums", "fun _ => #[]"),
        ("fixedTotals", "Array Int", "totals", "#[]"),
    ):
        lines.append(f"def {name} : Nat → {value_type}")
        lines += [f"  | {i} => {module}.{member}" for i, module in enumerate(modules)]
        lines += [f"  | _ => {fallback}", ""]
    lines += [
        "theorem fixedColumns_checked (B : Nat) (hB : B < 37) (j : Nat) (hj : j < 25) :",
        "    checkedColumn (fixedColumns B j) (fixedColumnSums B j) B j = true :=",
        "  match B, hB with",
    ]
    lines += [f"  | {i}, _ => {module}.column_arithmetic j hj" for i, module in enumerate(modules)]
    lines += [
        "  | B+37, h => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 37 B) h)", "",
        "theorem fixedTotals_checked (B : Nat) (hB : B < 37) :",
        "    checkedBlockTotals (fixedColumnSums B) (fixedTotals B) = true :=",
        "  match B, hB with",
    ]
    lines += [f"  | {i}, _ => {module}.block_arithmetic" for i, module in enumerate(modules)]
    lines += [
        "  | B+37, h => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 37 B) h)", "",
        "end DottieOriented.NativeSpectrum.MellinInteger", "",
    ]
    encoded = "\n".join(lines).encode("utf-8")
    (directory / "MellinIntegerTable.lean").write_bytes(encoded)
    return sha256(encoded).hexdigest()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--block", type=int, choices=range(37), help="generate one block for testing")
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    ctx.prec = 192
    weights = interpolation_weights()
    denominator = lcm(*(weight.denominator for weight in weights))
    integer_weights = tuple(int(weight * denominator) for weight in weights)
    blocks = range(37) if args.block is None else (args.block,)
    for block in blocks:
        digest = write_block(args.directory, block, *block_payload(block, integer_weights))
        print(f"MellinIntegerBlock{block:02d}  {digest}")
    if args.block is None:
        print(f"MellinIntegerTable  {write_table(args.directory)}")


if __name__ == "__main__":
    main()
