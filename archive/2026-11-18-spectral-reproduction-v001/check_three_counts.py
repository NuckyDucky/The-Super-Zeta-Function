"""Replay the three full-strip counts with FLINT's global counter and direct Hardy signs.

Run with Python 3.12 and python-flint==0.9.0 (tested with FLINT 3.6.0).
Inputs are the published rational brackets and local winding counts. Each
endpoint and interior seam gets a separate guarded global count. No contour
interpolant or seven-eighths bound is used in this calculation.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

import flint
from flint import acb, arb, ctx

ARCHIVE = Path(__file__).resolve().parent.parent
DISTANCE = ARCHIVE / "2026-11-18-superzeta-distance-v001"
MATCH = ARCHIVE / "2026-11-17-dottie-grid-match-v001"
sys.path.insert(0, str(DISTANCE))
from coverage_chart import ball, harmonic_height


def published_cells(k):
    if k == 1:
        record = json.loads((MATCH / "dottie-grid-certificate.json").read_bytes())
        broad = record["arms"]["dottie"]["broad"]
        edges = [Fraction(-1, 4), Fraction(0), Fraction(1, 4)]
        counts = [part["count"] for part in broad["pieces"]]
        brackets = [(entry, None) for entry in broad["line_brackets"]]
    else:
        record = json.loads((DISTANCE / f"coverage-h{k}.json").read_bytes())
        cells = record["cells"]
        edges = [Fraction(i, 4) for i in range(-2, 3)]
        assert [list(map(Fraction, c["offsets"])) for c in cells] == [
            [a, b] for a, b in zip(edges, edges[1:])
        ]
        counts = [c["count"] for c in cells]
        brackets = [(b["offset"], b["endpoint_signs"]) for c in cells for b in c["brackets"]]
    return edges, counts, [(Fraction(a), Fraction(b), signs) for (a, b), signs in brackets]


def hardy_sign(t):
    theta = acb(ball("1/4"), t / 2).lgamma().imag - t * arb.pi().log() / 2
    value = acb(ball("1/2"), t).zeta() * acb(0, theta).exp()
    assert value.imag.contains(0)
    if value.real > 0:
        return 1
    if value.real < 0:
        return -1
    raise ArithmeticError("Unresolved Hardy sign")


def check(k, expected_total):
    edges, windings, brackets = published_cells(k)
    ctx.prec = 96
    height = harmonic_height(k)
    guard = arb(0, arb(2) ** -18)
    counts = []
    for edge in edges:
        count = (height + ball(edge) + guard).zeta_nzeros().unique_fmpz()
        if count is None:
            raise ArithmeticError(f"H{k}, offset {edge}: unresolved N(T)")
        counts.append(int(count))
    differences = [hi - lo for lo, hi in zip(counts, counts[1:])]
    assert differences == windings
    assert sum(differences) == expected_total == len(brackets)

    ctx.prec = 128
    height = harmonic_height(k)
    brackets.sort()
    assert all(left[1] < right[0] for left, right in zip(brackets, brackets[1:]))
    assert [sum(a < lo < hi < b for lo, hi, _ in brackets)
            for a, b in zip(edges, edges[1:])] == differences
    for lo, hi, saved_signs in brackets:
        signs = [hardy_sign(height + ball(t)) for t in (lo, hi)]
        assert signs[0] * signs[1] == -1
        assert saved_signs is None or signs == saved_signs
    print(f"H{k}: N(T) at guarded cuts {counts}; successive counts {differences}; "
          f"{expected_total} disjoint critical-line brackets.", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run this verifier with Python assertions enabled.")
    print(f"python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}", flush=True)
    for harmonic, total in enumerate((2, 5, 4), 1):
        check(harmonic, total)
