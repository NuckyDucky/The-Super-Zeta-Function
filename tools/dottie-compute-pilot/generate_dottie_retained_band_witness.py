"""Generate integer coefficient witnesses for one archived Dottie band.

Each row represents the norm ``int(lo) + index``. Its first two entries are
the signed coefficient and the exponent of 2 stripped from the norm. The
remaining entries describe one witness for the odd part:

* ``"mod4", divisor`` gives a coprime divisor congruent to 3 modulo 4.
* ``"sign", divisor, code`` gives a coprime divisor with rational sign -1.
  The code is twice a square root plus the twist bit at the large conductor.
* ``"factors", [[prime_index, exponent], ...]`` gives the factorization.
  Each indexed prime entry is ``[prime, root_of_minus_one_or_null]``.

Norm endpoints, divisors, primes, and prime roots use decimal strings. The
generator writes one compact JSON document to stdout.
"""

import argparse
import hashlib
from importlib.util import module_from_spec, spec_from_file_location
import json
import math
from pathlib import Path
import sys


ARCHIVE = Path("archive/2026-11-21-gaussian-rectangle-v001")
BANDS = (
    (1854467118035498894, 1854467118035634061),
    (3708934236071001884, 3708934236071268123),
    (7417868472142007863, 7417868472142536246),
)
LARGE_CONDUCTOR = 1414835497


def load_retained(path):
    spec = spec_from_file_location("_dottie_retained_archive", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Cannot load the archived coefficient evaluator at {path}")
    retained = module_from_spec(spec)
    spec.loader.exec_module(retained)
    return retained


def read_archived_pieces(path):
    pieces = sorted(json.loads(path.read_text(encoding="utf-8")), key=lambda row: row["lo"])
    pairs = list(zip(pieces[::2], pieces[1::2]))
    if len(pieces) != 6 or any(
        (first["lo"], second["hi"]) != band or first["hi"] + 1 != second["lo"]
        for (first, second), band in zip(pairs, BANDS)
    ):
        raise ValueError("The archive does not describe the three exact merged Dottie bands")
    return pieces


def selected_range(args):
    if args.range is not None:
        if args.offset or args.count is not None:
            raise ValueError("--offset and --count require --band")
        lo, hi = args.range
        for band, (first, last) in enumerate(BANDS, start=1):
            if first <= lo <= hi <= last:
                return band, lo, hi
        raise ValueError("The inclusive range must lie within one merged Dottie band")

    first, last = BANDS[args.band - 1]
    if args.offset < 0 or (args.count is not None and args.count <= 0):
        raise ValueError("The offset must be nonnegative and the count must be positive")
    lo = first + args.offset
    hi = last if args.count is None else lo + args.count - 1
    if not first <= lo <= hi <= last:
        raise ValueError("The selected interval extends beyond its merged band")
    return args.band, lo, hi


def square_root_mod(retained, value, modulus):
    residue = int(retained.fmpz(value).sqrtmod(retained.fmpz(modulus))) % modulus
    root = min(residue, modulus - residue)
    if root * root % modulus != value % modulus:
        raise ArithmeticError(f"Invalid square root modulo {modulus}")
    return root


def rational_sign_code(retained, divisor):
    residue = divisor % LARGE_CONDUCTOR
    symbol = pow(residue, (LARGE_CONDUCTOR - 1) // 2, LARGE_CONDUCTOR)
    if symbol not in (1, LARGE_CONDUCTOR - 1):
        raise ArithmeticError(f"Invalid large-conductor residue for sign witness {divisor}")
    twist = int(symbol == LARGE_CONDUCTOR - 1)
    target = (5 if twist else 1) * residue % LARGE_CONDUCTOR
    return 2 * square_root_mod(retained, target, LARGE_CONDUCTOR) + twist


def zero_witness(retained, odd, twos, divisor, kind):
    quotient, remainder = divmod(odd, divisor)
    if remainder or math.gcd(divisor, quotient) != 1:
        raise ArithmeticError(f"Invalid coprime divisor {divisor} of {odd}")
    row = [0, twos, kind, str(divisor)]
    if kind == "sign":
        row.append(rational_sign_code(retained, divisor))
    return row


def coefficient_row(retained, norm):
    twos = (norm & -norm).bit_length() - 1
    odd = norm >> twos
    if odd % 4 == 3:
        return zero_witness(retained, odd, twos, odd, "mod4")
    if retained.sign(odd, 0) == -1:
        return zero_witness(retained, odd, twos, odd, "sign")

    factors = sorted((int(p), int(e)) for p, e in retained.fmpz(odd).factor())
    if math.prod(p**e for p, e in factors) != odd:
        raise ArithmeticError(f"Factorization does not recover odd part {odd}")
    for p, e in factors:
        if e % 2 and p % 4 == 3:
            return zero_witness(retained, odd, twos, p**e, "mod4")
    for p, e in factors:
        if e % 2 and retained.sign(p, 0) == -1:
            return zero_witness(retained, odd, twos, p**e, "sign")

    coefficient = 1
    for p, e in factors:
        signs = retained.prime_signs(p)
        if p % 4 == 3:
            coefficient *= signs[0] ** (e // 2)
        else:
            a, b = signs
            coefficient *= sum(a**k * b ** (e - k) for k in range(e + 1))
    return [coefficient, twos, "factors", factors]


def coefficient_digest(rows):
    raw = ",".join(str(row[0]) for row in rows)
    return hashlib.sha256(raw.encode("ascii")).hexdigest()


def generate(retained, pieces, band, lo, hi):
    rows = [coefficient_row(retained, norm) for norm in range(lo, hi + 1)]
    archive_matches = []
    for piece in pieces:
        first, last = piece["lo"], piece["hi"]
        if lo <= first <= last <= hi:
            block = rows[first - lo : last - lo + 1]
            digest = coefficient_digest(block)
            if digest != piece["sha256"] or sum(abs(row[0]) for row in block) != piece["mass"]:
                raise ArithmeticError(f"Coefficients differ from the archived piece {first}–{last}")
            archive_matches.append([str(first), str(last), digest])

    primes = sorted({p for row in rows if row[2] == "factors" for p, _ in row[3]})
    prime_indices = {p: index for index, p in enumerate(primes)}
    prime_table = []
    for p in primes:
        root = str(square_root_mod(retained, p - 1, p)) if p % 4 == 1 else None
        prime_table.append([str(p), root])

    total = minimum = maximum = mass = nonzero = 0
    for row in rows:
        coefficient = row[0]
        total += coefficient
        minimum = min(minimum, total)
        maximum = max(maximum, total)
        mass += abs(coefficient)
        nonzero += coefficient != 0
        if row[2] == "factors":
            row[3] = [[prime_indices[p], e] for p, e in row[3]]

    return {
        "format": "dottie-retained-band-witness-v1",
        "band": band,
        "lo": str(lo),
        "hi": str(hi),
        "coefficient_sha256": coefficient_digest(rows),
        "archive_matches": archive_matches,
        "stats": {"sum": total, "min_prefix": minimum, "max_prefix": maximum,
                  "mass": mass, "nonzero": nonzero},
        "primes": prime_table,
        "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", type=Path, required=True, help="canonical Super Zeta checkout")
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--band", type=int, choices=range(1, 4),
                           help="one merged band in increasing norm order")
    selection.add_argument("--range", type=int, nargs=2, metavar=("FIRST", "LAST"),
                           help="an inclusive interval inside one merged band")
    parser.add_argument("--offset", type=int, default=0, help="skip norms from the start of --band")
    parser.add_argument("--count", type=int, help="number of norms from --band, defaulting to its end")
    args = parser.parse_args()

    try:
        band, lo, hi = selected_range(args)
        archive = args.repo.resolve() / ARCHIVE
        pieces = read_archived_pieces(archive / "carriers.json")
        retained = load_retained(archive / "retained.py")
        report = generate(retained, pieces, band, lo, hi)
    except ValueError as error:
        parser.error(str(error))
    except (ArithmeticError, ImportError, OSError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")

    json.dump(report, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
