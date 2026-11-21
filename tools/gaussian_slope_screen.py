"""Screen three fixed rectangle inputs at each subsequent whole-block cutoff."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import gzip
import hashlib
import json
from math import factorial
from pathlib import Path
import sys

from flint import acb, arb, ctx

from gaussian_intervening_slope import FINAL, REFERENCE, negative_slope, phase, value
from gaussian_moments import BITS, FROZEN, LAST, ORDER, WIDTH, compute_block
from gaussian_prefix_smoothing import prefix_bounds

LIMIT = 2**30
SAVED = Path(__file__).resolve().parents[1] / "archive/2026-11-21-gaussian-rectangle-v001/gaussian-slope-screen.json"


def sum_block(lo):
    lo, raw, nonzero, mass, sums = compute_block(lo)
    return lo, hashlib.sha256(raw).digest(), nonzero, mass, sums


def screen(workers):
    ctx.prec = BITS
    with gzip.open(FROZEN,"rt",encoding="utf-8") as stream:
        row = json.load(stream)["cutoffs"][str(LAST)]
    mass = arb(row["mass"])
    moments = [acb(arb(re),arb(im)) for re, im in row["moments"]]
    probes = [acb(0,-arb(35)/2048), acb(0,-arb(1)/512), acb(arb(63)/2048,arb(27)/2048)]
    names = ["line at bottom", "line at center height", "right edge at top"]
    smallest = [None]*len(probes)
    digest = hashlib.sha256()
    new_nonzero, screened, reversal = 0, 0, None
    _, smoothing = prefix_bounds(LIMIT, 11)
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for batch in range(LAST, LIMIT, 2*workers*WIDTH):
            jobs = range(batch,min(batch+2*workers*WIDTH,LIMIT),WIDTH)
            for lo, block_hash, nonzero, dm, jet in pool.map(sum_block, jobs):
                cutoff = lo+WIDTH
                mass += arb(dm)
                for k,(re,im) in enumerate(jet):
                    moments[k] += acb(arb(re),arb(im))/factorial(k)
                phase.arc.N, phase.arc.order = cutoff, ORDER
                phase.arc.mass, phase.arc.coeff_taylor = mass, moments
                if cutoff == REFERENCE:
                    scale = abs(value(acb(0,-arb(1)/512)))
                    assert scale > 0
                    smooth_radius = (smoothing/scale).upper()
                if cutoff <= FINAL:
                    continue
                new_nonzero += nonzero
                screened += 1
                digest.update(block_hash)
                for i,z in enumerate(probes):
                    reading = negative_slope(z,scale) + arb(0,smooth_radius)
                    if smallest[i] is None or reading.lower() < smallest[i][0]:
                        smallest[i] = (reading.lower(),cutoff,str(reading))
                    if reading < 0 and reversal is None:
                        reversal = {"cutoff":cutoff, "probe":names[i], "negative_slope":str(reading)}
                if cutoff % (32*WIDTH) == 0 or reversal:
                    print(f"Screened through {cutoff:,} of {LIMIT:,}", file=sys.stderr, flush=True)
                if reversal:
                    break
            if reversal:
                break
    return {"after_norm":FINAL, "planned_stop":LIMIT, "last_tested":cutoff,
            "step":WIDTH, "tested_cutoffs":screened, "additional_nonzero_coefficients":new_nonzero,
            "hash_of_ordered_raw_block_digests":digest.hexdigest(),
            "minimum_lower_reading_by_probe":[{"probe":name,"cutoff":entry[1],"negative_slope":entry[2]}
                                            for name,entry in zip(names,smallest,strict=True)],
            "first_strict_reversal":reversal, "smooth_slope_error_over_scale":str(smooth_radius)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if not __debug__ or args.workers < 1:
        parser.error("Use assertions and at least one worker")
    result = screen(args.workers)
    if result != json.loads(SAVED.read_text(encoding="utf-8")):
        raise ArithmeticError("Screen differs from the saved record")
    print(json.dumps(result,indent=2))
