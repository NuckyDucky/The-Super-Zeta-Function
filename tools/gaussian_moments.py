"""Rebuild the 193 Gaussian moment records from the quartic's conductor signs."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import gzip
import hashlib
import json
from math import factorial, isqrt
from pathlib import Path
import sys

import numpy as np
from flint import acb, arb, ctx

ARCHIVE = Path(__file__).resolve().parents[1] / "archive"
sys.path.insert(0, str(ARCHIVE / "2026-11-20-gaussian-reflected-disks-v001"))
from gaussian_inputs import CONDUCTOR, height

FROZEN = ARCHIVE / "2026-11-20-gaussian-circle-phases-v001" / "moments.json.gz"
FIRST = 2**26
LAST = 2**28
WIDTH = 2**20
ORDER = 16
BITS = 256
CUTOFFS = range(FIRST, LAST + 1, WIDTH)


def signed_counts(lo, hi):
    """One generator a+bi per ideal: a>0, b>=0, lo<a²+b²<=hi."""
    rows = range(1, isqrt(hi) + 1)
    first = np.fromiter((isqrt(lo-a*a) + 1 if a*a <= lo else 0 for a in rows),
                        dtype=np.int64, count=len(rows))
    after = np.fromiter((isqrt(hi-a*a) + 1 for a in rows), dtype=np.int64, count=len(rows))
    lengths = after - first
    a = np.repeat(np.arange(1, len(rows)+1, dtype=np.int64), lengths)
    starts = lengths.cumsum() - lengths
    b = np.arange(len(a), dtype=np.int64) + np.repeat(first-starts, lengths)
    norms = a*a + b*b

    signs = np.ones(len(a), dtype=np.int32)
    for p, root in CONDUCTOR:
        # All modular products are exact signed 64-bit integer operations.
        if p*p >= 2**63 or isqrt(hi)*(1+root) >= 2**63:
            raise OverflowError("Conductor exceeds the integer bounds for this enumerator")
        residues = (a + root*b) % p
        if p < 1024:
            table = np.array([pow(i, (p-1)//2, p) for i in range(p)])
            values = table[residues]
        else:
            exponent = (p-1)//2
            values = np.ones(len(a), dtype=np.int64)
            while exponent:
                if exponent & 1:
                    values = values*residues % p
                residues = residues*residues % p
                exponent //= 2
        if not np.all((values == 0) | (values == 1) | (values == p-1)):
            raise ArithmeticError("Invalid quadratic character value")
        signs *= np.where(values == p-1, -1, values).astype(np.int32)

    # At a fixed norm each a contributes at most once, hence |a_n|<=sqrt(hi).
    counts = np.zeros(hi-lo, dtype="<i4")
    np.add.at(counts, norms-lo-1, signs)
    return counts


def compute_block(lo):
    ctx.prec = BITS
    counts = signed_counts(lo, lo+WIDTH)
    exponent = acb(-arb(1)/2, -height())
    mass = arb(0)
    sums = [acb(0) for _ in range(ORDER+1)]
    nonzero = np.flatnonzero(counts)
    for i in nonzero:
        log_n = arb(lo+int(i)+1).log()
        term = int(counts[i]) * (exponent*log_n).exp()
        mass += abs(term)
        neg_log = -log_n
        for k in range(ORDER):
            sums[k] += term
            term *= neg_log
        sums[ORDER] += term
    return (lo, counts.tobytes(), len(nonzero), str(mass),
            [(str(z.real), str(z.imag)) for z in sums])


def archived_contains(outer, inner):
    # Use exact rationals for the literal decimal endpoints of both saved
    # enclosures. Comparing binary re-parsings could enlarge the outer ball.
    def endpoints(text):
        mid, rad = map(Fraction, text.removeprefix("[").removesuffix("]").split(" +/- "))
        if rad < 0:
            raise ValueError("Negative radius in moment record")
        return mid-rad, mid+rad

    left, right = endpoints(outer)
    low, high = endpoints(inner)
    return left <= low <= high <= right


def compare_rows(cutoff, old, new):
    for key in ("norm_sha256", "nonzero", "divided_by_factorial"):
        if new[key] != old[key]:
            raise ArithmeticError(f"N={cutoff}: {key} differs")
    if not archived_contains(old["mass"], new["mass"]):
        raise ArithmeticError(f"N={cutoff}: mass outside archived interval")
    for k, (v, w) in enumerate(zip(old["moments"], new["moments"], strict=True)):
        if not all(archived_contains(p, q) for p, q in zip(v, w, strict=True)):
            raise ArithmeticError(f"N={cutoff}: moment {k} outside archived interval")


def regenerate(output_path: Path, workers: int = 4):
    """Write a new gzip table after checking every cutoff against the deposit."""
    output_path = Path(output_path).resolve()
    if workers < 1:
        raise ValueError("Select at least one worker")
    if output_path.is_relative_to(ARCHIVE) or output_path.exists():
        raise ValueError("Choose a new output file outside the preserved archive")
    if not output_path.parent.is_dir():
        raise ValueError("Choose an existing directory for the generated table")
    with gzip.open(FROZEN, "rt", encoding="utf-8") as source:
        frozen = json.load(source)
    if (frozen["planned_norm_endpoints"] != list(CUTOFFS)
            or sorted(map(int, frozen["cutoffs"])) != list(CUTOFFS)
            or frozen["order"] != ORDER or frozen["bits"] != 192):
        raise ValueError("Unexpected archived cutoff schedule, precision, or order")
    ctx.prec = BITS
    digest = hashlib.sha256(bytes(4))  # Archived signed int32 little endian a_0=0.
    mass, total_nonzero = arb(0), 0
    total = [acb(0) for _ in range(ORDER+1)]
    factors = [factorial(k) for k in range(ORDER+1)]
    records, checks = {}, {}
    check_norms = sorted(map(int, frozen["signed_integer_checks"]))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        # The parent needs coefficient bytes in increasing norm order for
        # the cumulative hashes. Bound the number of outstanding blocks.
        for batch in range(0, LAST, workers*2*WIDTH):
            starts = range(batch, min(LAST, batch+workers*2*WIDTH), WIDTH)
            for lo, raw, nonzero, partial_mass, sums in pool.map(compute_block, starts):
                hi = lo + WIDTH
                digest.update(raw)
                counts = np.frombuffer(raw, dtype="<i4")
                for n in check_norms:
                    if lo < n <= hi:
                        checks[str(n)] = int(counts[n-lo-1])
                total_nonzero += nonzero
                mass += arb(partial_mass)
                for k, (re, im) in enumerate(sums):
                    total[k] += acb(arb(re), arb(im)) / factors[k]
                if hi in CUTOFFS:
                    row = dict(norm_sha256=digest.hexdigest(), nonzero=total_nonzero,
                               mass=str(mass), divided_by_factorial=True,
                               moments=[[str(z.real), str(z.imag)] for z in total])
                    compare_rows(hi, frozen["cutoffs"][str(hi)], row)
                    records[str(hi)] = row
                if hi % (16*WIDTH) == 0:
                    print(f"Norm {hi:,}/{LAST:,}; {len(records)} verified cutoffs", flush=True)
    if checks != frozen["signed_integer_checks"]:
        raise ArithmeticError("The archived individual signed coefficients differ")
    document = dict(bits=BITS, order=ORDER, intervals="closed right endpoint, open left endpoint",
                    planned_norm_endpoints=list(CUTOFFS), signed_integer_checks=checks,
                    cutoffs=records)
    # 'xb' also prevents two simultaneous runs overwriting each other's result.
    encoded = gzip.compress((json.dumps(document, indent=2) + "\n").encode(), mtime=0)
    with output_path.open("xb") as target:
        target.write(encoded)
    print(f"Verified {len(records)} hashes, counts and masses, "
          f"{len(records)*(ORDER+1)} complex moments, and {len(checks)} individual coefficients.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new gzip table outside archive/")
    parser.add_argument("--workers", type=int, default=4, help="number of CPU processes")
    args = parser.parse_args()
    regenerate(args.output, args.workers)
