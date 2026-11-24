"""Translate a bounded witness-generator slice into a Lean certificate.

Input is JSON from generate_dottie_retained_band_witness.py. Use a file path
or `-` for stdin. Offsets are relative to the first norm in the input JSON.
The output's rootIndices maps each factor prime to its Lucas table index.
Use --block to issue and join certificates for several consecutive chunks.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


MAX_ROWS = 256
MAX_BLOCK_ROWS = 4096
SMALL_PRIME_LIMIT = 256
WORD_LIMIT = 2**64


def natural(value):
    if type(value) is int and value >= 0:
        return value
    if isinstance(value, str) and value.isascii() and value.isdecimal():
        return int(value)
    raise ValueError(f"Expected a natural number, got {value!r}")


def select_rows(report, offset, count, limit=MAX_ROWS):
    if not isinstance(report, dict) or report.get("format") != "dottie-retained-band-witness-v1":
        raise ValueError("Expected dottie-retained-band-witness-v1 input")
    lo, hi = natural(report["lo"]), natural(report["hi"])
    rows = report["rows"]
    if not 0 < lo <= hi < WORD_LIMIT or len(rows) != hi - lo + 1:
        raise ValueError("The JSON rows do not cover their stated positive norm range")
    count = len(rows) - offset if count is None else count
    if offset < 0 or count < 1 or offset + count > len(rows):
        raise ValueError("The selected rows must lie within the JSON input")
    if count > limit:
        raise ValueError(f"Select at most {limit} rows using --offset and --count")
    return lo + offset, rows[offset : offset + count]


def row_terms(start, rows, prime_table):
    terms, values, roots = [], [], set()
    for norm, row in enumerate(rows, start=start):
        value, twos, kind, *payload = row
        twos = natural(twos)
        if type(value) is not int or twos >= 64:
            raise ValueError(f"Invalid coefficient or dyadic exponent at norm {norm}")
        odd = norm >> twos
        if odd % 2 != 1 or odd << twos != norm:
            raise ValueError(f"Invalid dyadic decomposition at norm {norm}")
        values.append(value)

        if kind in ("mod4", "sign"):
            if value != 0 or len(payload) != (1 if kind == "mod4" else 2):
                raise ValueError(f"Invalid zero row at norm {norm}")
            divisor = natural(payload[0])
            if not divisor or odd % divisor or math.gcd(divisor, odd // divisor) != 1:
                raise ValueError(f"Invalid coprime divisor at norm {norm}")
            if kind == "mod4" and divisor % 4 != 3:
                raise ValueError(f"Invalid mod-four divisor at norm {norm}")
            sign_code = f"(some {natural(payload[1])})" if kind == "sign" else "none"
            terms.append(f".zero {twos} {divisor} {sign_code}")
        elif kind == "factors" and len(payload) == 1:
            factors, product, seen = [], 1, set()
            for index, exponent in payload[0]:
                index, exponent = natural(index), natural(exponent)
                if index >= len(prime_table) or not 1 <= exponent <= 64:
                    raise ValueError(f"Invalid factor entry at norm {norm}")
                p_text, root_text = prime_table[index]
                p = natural(p_text)
                if not 2 <= p < WORD_LIMIT or p in seen:
                    raise ValueError(f"Invalid or repeated factor prime at norm {norm}")
                if root_text is None:
                    if p % 4 != 3:
                        raise ValueError(f"Missing split root for prime {p}")
                    root_term = "none"
                else:
                    root = natural(root_text)
                    if p % 4 != 1 or root >= p or (root * root + 1) % p:
                        raise ValueError(f"Invalid split root for prime {p}")
                    root_term = f"some {root}"
                seen.add(p)
                roots.add(p)
                product *= p**exponent
                factors.append(f"⟨{p}, {exponent}, {root_term}⟩")
            if product != odd:
                raise ValueError(f"Factor product does not recover the odd part at norm {norm}")
            signed = f"({value})" if value < 0 else str(value)
            terms.append(f".factored {twos} [{', '.join(factors)}] {signed}")
        else:
            raise ValueError(f"Unknown or malformed row witness at norm {norm}")
    return terms, values, roots


def lucas_terms(roots):
    if not roots:
        return [], []

    from flint import fmpz

    nodes, pending = {}, list(sorted(roots, reverse=True))
    while pending:
        p = pending.pop()
        if p in nodes:
            continue
        if p <= SMALL_PRIME_LIMIT:
            if p < 2 or any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
                raise ValueError(f"Invalid small-prime leaf {p}")
            nodes[p] = None
            continue
        if not fmpz(p).is_prime():
            raise ValueError(f"Factor {p} is composite")
        powers = sorted((int(q), int(e)) for q, e in fmpz(p - 1).factor())
        if (any(not 2 <= q < p or e < 1 for q, e in powers)
                or math.prod(q**e for q, e in powers) != p - 1):
            raise ArithmeticError(f"Incomplete factorization of {p} - 1")
        g = next(g for g in range(2, p) if pow(g, p - 1, p) == 1
                 and all(pow(g, (p - 1) // q, p) != 1 for q, _ in powers))
        nodes[p] = (g, powers)
        pending.extend(q for q, _ in powers)

    indices = {p: i for i, p in enumerate(sorted(nodes))}
    terms = []
    for p in indices:
        if nodes[p] is None:
            terms.append(f".leaf {p}")
            continue
        g, powers = nodes[p]
        refs = [str(indices[q]) for q, e in powers for _ in range(e)]
        terms.append(f".lucas {p} {g} [{', '.join(refs)}]")
    return terms, [(p, indices[p]) for p in sorted(roots)]


def lean_collection(terms, opening):
    if not terms:
        return opening + "]"
    return opening + "\n" + ",\n".join(f"  {term}" for term in terms) + "\n]"


def signed_prefix_summary(values):
    total = lower = upper = 0
    for value in values:
        total += value
        lower = min(lower, total)
        upper = max(upper, total)
    return total, lower, upper


IMPORTS = "import DottieBandLucasCheck\nimport DottieBandChunkReplay\n\n"


def render(start, rows, primes, root_indices, values, include_imports=True):
    size = len(rows)
    namespace = f"DottieBandWitness{start}_{size}"
    total, lower, upper = signed_prefix_summary(values)
    digest = hashlib.sha256(",".join(map(str, values)).encode("ascii")).hexdigest()
    index_terms = [f"({p}, {i})" for p, i in root_indices]
    return (IMPORTS if include_imports else "") + f"""namespace QuarticModel
namespace {namespace}

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 3000000

-- Norms {start} through {start + size - 1}, {size} rows, {len(primes)} prime nodes.
-- SHA-256 of the signed coefficient sequence: {digest}
def startNorm : Nat := {start}
def rowCount : Nat := {size}
def primeTable : Array DottieBandPrimeNode := {lean_collection(primes, '#[')}

def rootIndices : List (Nat × Nat) := {lean_collection(index_terms, '[')}

def rows : List DottieBandRow := {lean_collection(rows, '[')}

def expected : DottieBandSummary := ⟨{total}, {lower}, {upper}⟩

private theorem primeTableChecked :
    (List.range primeTable.size).all (dottieBandPrimeTableCheck primeTable) = true := by
  decide +kernel

theorem certificate : DottieBandChunk startNorm rowCount expected :=
  dottie_band_check_rows_sound (dottie_band_prime_root_ok_sound (roots := rootIndices) primeTableChecked)
    (rows := rows) (by decide +kernel)

end {namespace}
end QuarticModel
"""


def join_certificates(names, depth=1):
    if len(names) == 1:
        return names[0]
    middle = len(names) // 2
    indent = "  " * (depth + 1)
    left = join_certificates(names[:middle], depth + 1)
    right = join_certificates(names[middle:], depth + 1)
    return f"(dottie_band_append_chunks\n{indent}{left}\n{indent}{right})"


def render_block(start, selected, prime_table):
    chunks, names, coefficients = [], [], []
    for offset in range(0, len(selected), MAX_ROWS):
        first = start + offset
        terms, values, roots = row_terms(first, selected[offset:offset + MAX_ROWS], prime_table)
        primes, indices = lucas_terms(roots)
        chunks.append(render(first, terms, primes, indices, values, include_imports=False))
        names.append(f"DottieBandWitness{first}_{len(terms)}.certificate")
        coefficients.extend(values)

    total, lower, upper = signed_prefix_summary(coefficients)
    namespace = f"DottieBandBlock{start}_{len(selected)}"
    return IMPORTS + "\n".join(chunks) + f"""
namespace QuarticModel
namespace {namespace}

theorem certificate : DottieBandChunk {start} {len(selected)} ⟨{total}, {lower}, {upper}⟩ :=
  {join_certificates(names)}

#print axioms certificate

end {namespace}
end QuarticModel
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("input", help="witness JSON path, or - for standard input")
    parser.add_argument("--offset", type=int, default=0, help="skip this many input rows")
    parser.add_argument("--count", type=int, help="select this many rows")
    parser.add_argument("--block", action="store_true", help="join up to 4096 consecutive rows")
    args = parser.parse_args()

    try:
        if args.input == "-":
            report = json.load(sys.stdin.buffer)
        else:
            report = json.loads(Path(args.input).read_text(encoding="utf-8-sig"))
        limit = MAX_BLOCK_ROWS if args.block else MAX_ROWS
        start, selected = select_rows(report, args.offset, args.count, limit)
        if args.block:
            result = render_block(start, selected, report["primes"])
        else:
            rows, values, roots = row_terms(start, selected, report["primes"])
            primes, indices = lucas_terms(roots)
            result = render(start, rows, primes, indices, values)
    except (KeyError, TypeError, ValueError) as error:
        parser.error(str(error))
    except (ArithmeticError, ImportError, OSError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")

    sys.stdout.buffer.write(result.encode("utf-8"))


if __name__ == "__main__":
    main()
