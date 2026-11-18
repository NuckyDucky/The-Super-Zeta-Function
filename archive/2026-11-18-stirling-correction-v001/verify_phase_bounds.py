"""Check the rational hypotheses of Lean's dottie_quartet_bracket."""
import json
import sys
from functools import cache
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx, fmpq


ARCHIVE = Path(__file__).resolve().parents[1]
FOUNDATION = ARCHIVE / "2026-11-16-super-zeta-v001" / "computations"
NOMINATION = ARCHIVE / "2026-11-17-dottie-grid-match-v001" / "dottie-grid-nomination.json"
SCALE = 10**25
BOUNDS = (
    (424329, -2510834912, -2510834911, 1),
    (424330, -2510818023, -2510818022, -1),
)


def main():
    if not __debug__:
        raise RuntimeError("The certificate requires Python assertions.")
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(FOUNDATION))
    from verify_binomial_normalization import STEPS, isolate

    ctx.prec = 384

    @cache
    def radius_data(n):
        return isolate(n)

    def radial_log(n):
        radius, _, _ = radius_data(n)
        return (radius / (2*arb.pi()*n)).log()

    source = json.loads(NOMINATION.read_text(encoding="utf-8"))
    parameters = source["source_exact_decimals"]
    x, y = (arb(fmpq(q.numerator, q.denominator))
            for q in (Fraction(parameters[key]) for key in ("x", "y")))
    stages = source["scalar_period"]
    delta = ((x/y)**2).log1p() * stages / 2
    height = 2*arb.pi()/delta
    increments = []
    for n, lo, hi, sign in BOUNDS:
        radial = radial_log(n+1) - radial_log(n)
        assert arb(fmpq(lo, SCALE)) < radial < arb(fmpq(hi, SCALE))
        factorial = (arb(1)/(4*n*(n+1))).log1p()
        excess = height/2*(factorial+radial)-arb.pi()
        assert sign*excess > 0
        increments.append({
            "level": n,
            "lower_numerator": lo,
            "upper_numerator": hi,
            "denominator": SCALE,
            "radial_increment": radial.str(31),
            "phase_minus_pi_radians": excess.str(22),
        })
    roots = []
    for n in sorted({n+j for n, _, _, _ in BOUNDS for j in (0, 1)}):
        _, lo, hi = radius_data(n)
        roots.append({"level": n, "t_lower": str(lo), "t_upper": str(hi)})
    print(json.dumps({
        "arb_bits": ctx.prec,
        "bisections_per_root": STEPS,
        "t_brackets": roots,
        "increments": increments,
    }, indent=2))


if __name__ == "__main__":
    main()
