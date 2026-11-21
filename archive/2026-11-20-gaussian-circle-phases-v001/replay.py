"""Enclose the spiral phase of each finite signed sum on both complete circles."""
import argparse
import gzip
import json
import math
import sys
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
DISKS = HERE.parent / "2026-11-20-gaussian-reflected-disks-v001"
LIFT = HERE.parent / "2026-11-19-dottie-plane-atlas-v001" / "atlas" / "phase_lift.json"
sys.path.insert(0, str(DISKS))
from gaussian_inputs import Q, height

ctx.prec = 192
TAU = 2 * arb.pi()
TARGET = arb(39) / 10
CLEARANCE = arb(91) / 100
RADIUS = arb(31) / 2048
re, im = map(arb, json.loads(LIFT.read_text())["lifted_log_multiplier"])
KAPPA = (im + TAU) / re

spec = spec_from_file_location("gaussian_arcs", DISKS / "arc-gaussian.py")
arc = module_from_spec(spec)
spec.loader.exec_module(arc)
arc.T = height()
arc.B = arb(Q).sqrt() / TAU
arc.logBt = acb((arc.B * arc.T).log(), arb.pi() / 2)
s0 = acb(arb(1) / 2, arc.T)
arc.gamma0 = ((s0 - 2) * arc.B.log() + s0.lgamma() - acb(2, arc.T).lgamma().real).exp()


def coords(theta, mirror):
    x = arb(1) / 64 + RADIUS * theta.cos()
    y = -arb(1) / 512 + RADIUS * theta.sin()
    return acb(-x if mirror else x, y)


def reading(theta, mirror):
    z = coords(theta, mirror)
    f = arc.partial(z.real + arb(1) / 2, z.imag)
    return f / arc.gamma(z)


def relative_phase(value, anchor):
    quotient = value / anchor
    if quotient.real > 0:
        return anchor.arg() + quotient.arg() - KAPPA * abs(value).log()
    return None


def log_derivative_term(z):
    h = arc.prefix(z)
    c = arc.B.log() + (s0 + z).digamma()
    deriv = acb(0)
    for k in range(arc.order, 0, -1):
        deriv = deriv * z + k * arc.coeff_taylor[k]
    ln = arb(arc.N).log()
    u = abs(z) * ln
    err = (arc.mass * ln * u.exp() * u**arc.order / math.factorial(arc.order)).upper()
    deriv += acb(arb(0, err), arb(0, err))
    return h, c * h + arc.gamma(z) * deriv, c


def left_phase_velocity(theta):
    z = coords(theta, True)
    h, dh, c = log_derivative_term(z)
    hstar, dhstar, _ = log_derivative_term(-z.conjugate())
    dz = RADIUS * acb(theta.sin(), theta.cos())
    log_deriv = dz * ((dh - dhstar.conjugate()) / (h + hstar.conjugate()) - c)
    return log_deriv.imag - KAPPA * log_deriv.real


def check_sector(lo, hi, mirror):
    theta = lo.union(hi)
    center = reading((lo + hi) / 2, mirror).mid()
    value = reading(theta, mirror)
    if not abs(center) > 0 or not abs(value) > 0:
        return None
    phase = relative_phase(value, center)
    if phase is None or not phase.is_finite():
        return None
    # Select the closest representative of the target and check its two neighbors.
    # Containing the whole sector inside its one-turn neighborhood excludes all others.
    index = round(float(((phase.mid() - TARGET) / TAU).mid()))
    level = TARGET + index * TAU
    if not abs(phase - level) < TAU:
        return None
    levels = [level - TAU, level, level + TAU]
    if not mirror:
        return [] if all(abs(phase - target) > CLEARANCE for target in levels) else None
    possible = [target for target in levels if (phase - target).contains(0)]
    if not possible:
        return []
    velocity = left_phase_velocity(theta)
    if not (velocity > 0 or velocity < 0):
        return None
    start = relative_phase(reading(lo, True), center)
    end = relative_phase(reading(hi, True), center)
    if start is None or end is None:
        return None
    signs = []
    for target in possible:
        a, b = start - target, end - target
        if a.contains(0) or b.contains(0):
            return None
        if a < 0 < b:
            signs.append(1)
        if b < 0 < a:
            signs.append(-1)
    return signs


def crossings(lo, hi, mirror, depth=0):
    found = check_sector(lo, hi, mirror)
    if found is not None:
        return found
    if depth >= 18:
        raise ArithmeticError(f"Unresolved arc at cutoff {arc.N}: {lo}, {hi}")
    mid = (lo + hi) / 2
    return crossings(lo, mid, mirror, depth + 1) + crossings(mid, hi, mirror, depth + 1)


def verify(cutoff, record):
    assert record["divided_by_factorial"]
    arc.N = cutoff
    arc.mass = arb(record["mass"])
    arc.coeff_taylor = [acb(arb(x), arb(y)) for x, y in record["moments"]]
    arc.order = len(arc.coeff_taylor) - 1
    grid = [TAU * j / 256 for j in range(257)]
    for mirror, expected in ((False, []), (True, [-1, 1])):
        signs = []
        for lo, hi in zip(grid, grid[1:]):
            signs.extend(crossings(lo, hi, mirror))
        if signs != expected:
            raise ArithmeticError(f"Cutoff {cutoff}, mirror={mirror}, crossings={signs}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, help="Replay one recorded norm cutoff.")
    args = parser.parse_args()
    with gzip.open(HERE / "moments.json.gz", "rt") as stream:
        data = json.load(stream)
    records = data["cutoffs"]
    cutoffs = sorted(map(int, records))
    assert cutoffs == list(range(2**26, 2**28 + 1, 2**20))
    if args.cutoff is not None and args.cutoff not in cutoffs:
        parser.error("Choose one of the 193 recorded cutoffs.")
    selected = [args.cutoff] if args.cutoff is not None else cutoffs
    for cutoff in selected:
        verify(cutoff, records[str(cutoff)])
        if cutoff == 2**28:
            east = abs(arc.partial(arb(33)/64 + RADIUS, -arb(1)/512))
            assert arb("1.8787e-28") < east < arb("1.8788e-28")
            print(f"Final cutoff, eastern boundary, completed finite modulus: {east}")
    print(f"{len(selected)} cutoffs passed: right clearance > 0.91 rad; left crossings (-1,+1).")


if __name__ == "__main__":
    main()

