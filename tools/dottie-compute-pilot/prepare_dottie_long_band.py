"""Prepare deterministic Lean sources for one archived long Dottie band.

With no --blocks limit, prepare the entire long interval. With --blocks,
prepare exactly that many full blocks from its lower endpoint. An existing
output can be reused if every generated file and the index match byte for byte.
"""

import argparse
import hashlib
import json
from pathlib import Path

import emit_dottie_band_lean as emitter
import generate_dottie_retained_band_witness as generator


LONG_WIDTHS = (131072, 262144, 524288)


def source_record(module, content, begin, end, summary, coefficient_sha256):
    total, lower, upper = summary
    return {
        "module": module,
        "file": f"{module}.lean",
        "begin": str(begin),
        "end": str(end),
        "rows": end - begin + 1,
        "expected": {"sum": total, "min_prefix": lower, "max_prefix": upper},
        "coefficient_sha256": coefficient_sha256,
        "source_bytes": len(content),
        "source_sha256": hashlib.sha256(content).hexdigest(),
    }


def assembly_source(module, block_records, summary):
    first, last = block_records[0], block_records[-1]
    start = int(first["begin"])
    count = int(last["end"]) - start + 1
    total, lower, upper = summary
    imports = "\n".join(f'import {block["module"]}' for block in block_records)
    names = [f'DottieBandBlock{block["begin"]}_{block["rows"]}.certificate'
             for block in block_records]
    proof = emitter.join_certificates(names)
    return f"""{imports}

namespace QuarticModel
namespace {module}

set_option autoImplicit false
set_option maxRecDepth 24000

theorem certificate : DottieBandChunk {start} {count} ⟨{total}, {lower}, {upper}⟩ :=
  {proof}

#print axioms certificate

end {module}
end QuarticModel
""".encode("utf-8")


def prepare_sources(repo, band, block_size, blocks):
    if not 1 <= block_size <= emitter.MAX_BLOCK_ROWS:
        raise ValueError(f"--block-size must be in 1..{emitter.MAX_BLOCK_ROWS}")
    archive = repo.resolve() / generator.ARCHIVE
    pieces = generator.read_archived_pieces(archive / "carriers.json")
    long_piece = pieces[2 * (band - 1)]
    begin, archive_end = long_piece["lo"], long_piece["hi"]
    width = LONG_WIDTHS[band - 1]
    if archive_end - begin + 1 != width:
        raise ValueError(f"Unexpected archived long-band width for band {band}")
    if blocks is not None and not 1 <= blocks <= width // block_size:
        raise ValueError("--blocks must select a positive number of full leading blocks")

    count = width if blocks is None else blocks * block_size
    end = begin + count - 1
    retained = generator.load_retained(archive / "retained.py")
    report = generator.generate(retained, pieces, band, begin, end)
    rows, primes = report["rows"], report["primes"]
    if (int(report["lo"]), int(report["hi"]), len(rows)) != (begin, end, count):
        raise ArithmeticError("The witness report does not cover the selected long interval")
    if end == archive_end:
        expected_match = [str(begin), str(end), long_piece["sha256"]]
        if expected_match not in report["archive_matches"]:
            raise ArithmeticError("The complete long interval did not match its archived hash")

    stem = f"DottieLongBand{band}"
    sources, records = {}, []
    total = lower = upper = 0
    next_norm = begin
    for number, offset in enumerate(range(0, count, block_size), start=1):
        block_rows = rows[offset : offset + block_size]
        start = begin + offset
        stop = start + len(block_rows) - 1
        if start != next_norm or not start <= stop <= end:
            raise ArithmeticError("Source blocks are not contiguous")
        summary = emitter.signed_prefix_summary(row[0] for row in block_rows)
        block_total, block_lower, block_upper = summary
        lower = min(lower, total + block_lower)
        upper = max(upper, total + block_upper)
        total += block_total
        next_norm = stop + 1
        module = f"{stem}Block{number:06d}"
        content = emitter.render_block(start, block_rows, primes).encode("utf-8")
        record = source_record(module, content, start, stop, summary,
                               generator.coefficient_digest(block_rows))
        records.append({"number": number, **record})
        sources[record["file"]] = content

    summary = (total, lower, upper)
    expected = report["stats"]
    if next_norm != end + 1 or summary != (expected["sum"], expected["min_prefix"],
                                           expected["max_prefix"]):
        raise ArithmeticError("The joined block summaries do not cover the witness report")
    module = f"{stem}Assembly"
    content = assembly_source(module, records, summary)
    assembly = source_record(module, content, begin, end, summary, report["coefficient_sha256"])
    sources[assembly["file"]] = content
    index = {
        "format": "dottie-long-band-sources-v1",
        "band": band,
        "archive": {"begin": str(begin), "end": str(archive_end),
                    "coefficient_sha256": long_piece["sha256"], "mass": long_piece["mass"]},
        "block_size": block_size,
        "complete_archive_interval": end == archive_end,
        "blocks": records,
        "assembly": assembly,
    }
    return sources, f"{stem}Index.json", index


def verify_bytes(path, content):
    if path.read_bytes() != content:
        raise FileExistsError(f"Output differs from the planned bytes: {path}")


def write_exact(path, content):
    try:
        target = path.open("xb")
    except FileExistsError:
        verify_bytes(path, content)
        return
    try:
        with target:
            target.write(content)
    except OSError:
        path.unlink(missing_ok=True)
        raise
    verify_bytes(path, content)


def write_sources(out, sources, index_name, index):
    out.mkdir(parents=True, exist_ok=True)
    index_path = out / index_name
    index_bytes = (json.dumps(index, indent=2) + "\n").encode("utf-8")
    if index_path.exists():
        verify_bytes(index_path, index_bytes)
    for name, content in sources.items():
        path = out / name
        if path.exists():
            verify_bytes(path, content)
    for name, content in sources.items():
        write_exact(out / name, content)
    write_exact(index_path, index_bytes)
    return index_path


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--band", type=int, choices=(1, 2, 3), required=True)
    parser.add_argument("--repo", type=Path, required=True, help="canonical Super Zeta checkout")
    parser.add_argument("--out", type=Path, required=True, help="directory for generated sources")
    parser.add_argument("--block-size", type=int, default=emitter.MAX_BLOCK_ROWS,
                        help="rows per module, from 1 through 4096 (default 4096)")
    parser.add_argument("--blocks", type=int, help="select this many full leading blocks")
    args = parser.parse_args()

    try:
        sources, name, index = prepare_sources(args.repo, args.band, args.block_size, args.blocks)
        path = write_sources(args.out, sources, name, index)
    except ValueError as error:
        parser.error(str(error))
    except (ArithmeticError, ImportError, OSError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")

    print(f'Prepared {len(index["blocks"])} blocks covering {index["assembly"]["rows"]} rows')
    print(path)


if __name__ == "__main__":
    main()
