"""Count ordinary zeta zeros and put both Gaussian bounds in the same units."""
import json
from pathlib import Path

from flint import acb, arb, ctx

from gaussian_inputs import Q, height


def main():
    ctx.prec = 160
    here = Path(__file__).resolve().parent
    earlier = here.parent / "2026-11-20-gaussian-two-root-transition-v001"
    corridor = json.loads((earlier / "gaussian-target-corridor.json").read_bytes())
    radius = arb(corridor["core_radius_upper"])
    base = json.loads((here / "gaussian-base-endpoints.json").read_bytes())
    center = height()
    log_b = (arb(Q).sqrt() / (2 * arb.pi())).log()
    log_scale = 2 * log_b + acb(2, center).lgamma().real
    rows = []
    for offset, row in zip((-1, 1), base["rows"], strict=True):
        t = center + arb(offset) / 16
        assert row["offset"] == f"{offset}/16" and arb(row["t"]).overlaps(t)
        assert arb(row["base_hardy_product"]) > 0
        # Bound N(t) at both ends of the height enclosure. Monotonicity then
        # gives the same exact integer at the Dottie endpoint whenever they agree.
        lo = t.lower().zeta_nzeros().unique_fmpz()
        hi = t.upper().zeta_nzeros().unique_fmpz()
        if lo is None or hi is None or lo != hi:
            raise ArithmeticError("Ordinary zeta count unresolved at an endpoint")
        log_scale_ratio = log_b / 2 + acb(arb(1) / 2, t).lgamma().real - log_scale
        ratio = log_scale_ratio.exp()
        rows.append(dict(offset=row["offset"], zeta_count=int(lo), base_sign=1,
                         f_over_H=str(ratio), hardy_abs_upper_from_corridor=str((radius / ratio).upper())))
    print(json.dumps(dict(precision_bits=ctx.prec, rows=rows,
                          riemann_zero_count_in_window=rows[1]["zeta_count"]-rows[0]["zeta_count"]), indent=2))


if __name__ == "__main__":
    main()
