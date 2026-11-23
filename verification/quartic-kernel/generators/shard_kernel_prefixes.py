"""Place independent closed kernel reductions in small compilation units."""
import argparse
from pathlib import Path
import re


BAND = re.compile(
    r"^private (theorem a\d+_\d+_\d+_band\d+ : bandStats [^\n]+ := by decide \+kernel)\n",
    re.M,
)


def shard_block(source, destination, batch_size):
    contents = source.read_text(encoding="utf-8-sig")
    proofs = BAND.findall(contents)
    if not proofs:
        raise ValueError(f"No band reductions in {source}")

    imports = []
    for start in range(0, len(proofs), batch_size):
        part = source.stem + f"Part{start // batch_size:03}"
        imports.append(f"import KernelNumerics.{part}\n")
        proof_body = "\n".join(proofs[start:start + batch_size])
        unit = (
            "import QuarticAnnulusBands\n\n"
            "namespace QuarticKernel.KernelPrefixes\n\n"
            "set_option maxRecDepth 24000\n"
            "set_option maxHeartbeats 0\n"
            "set_option Elab.async false\n\n"
            f"{proof_body}\n\n"
            "end QuarticKernel.KernelPrefixes\n"
        )
        (destination / "KernelNumerics" / f"{part}.lean").write_text(unit, encoding="utf-8")

    merged = BAND.sub("", contents)
    merged = merged.replace("import QuarticAnnulusBands\n", "".join(imports), 1)
    (destination / "KernelPrefixes" / source.name).write_text(merged, encoding="utf-8")
    return len(proofs), len(imports)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--first", type=int, required=True)
    parser.add_argument("--last", type=int, default=180)
    parser.add_argument("--batch-size", type=int, default=4)
    args = parser.parse_args()
    if args.batch_size < 1 or args.first < 0 or args.last < args.first:
        parser.error("choose a positive batch size and a nonempty block range")
    for folder in ("KernelNumerics", "KernelPrefixes"):
        (args.destination / folder).mkdir(parents=True, exist_ok=True)
    proofs = parts = 0
    for block in range(args.first, args.last + 1):
        proofs_count, parts_count = shard_block(
            args.source / f"Block{block:02}.lean", args.destination, args.batch_size
        )
        proofs += proofs_count
        parts += parts_count
    print(f"Placed {proofs} existing reductions in {parts} compilation units.")


if __name__ == "__main__":
    main()
