"""Draw the certified endpoint heights and slope bounds of the 64 added blocks."""
import json
from pathlib import Path

import matplotlib.pyplot as plt
from flint import arb

ROOT = Path(__file__).resolve().parents[1]


def main():
    record = json.loads((ROOT / "archive/2026-11-21-gaussian-rectangle-v001/gaussian-intervening-slope.json").read_text())
    rows = [r for r in record["rows"] if r["through_norm"] > record["previous_slope_cutoff"]]
    ends = [r["through_norm"] / 1e6 for r in rows]
    start = record["previous_slope_cutoff"] / 1e6
    heights = [sum(map(float, r["root_offset_from_T_D"])) / 2 for r in rows]
    endpoint = [float(r["negative_slope_lower"]) for r in rows]
    within = [float(arb(r["all_integer_cutoffs_in_block"]["negative_slope_lower"]).mid()) for r in rows]
    fig, (height, slope) = plt.subplots(2, 1, figsize=(8, 5.4), sharex=True,
                                       layout="constrained")
    for ax in (height, slope):
        ax.set_facecolor("#fbfaf6")
        ax.spines[["right", "top"]].set_visible(False)
        ax.grid(axis="y", color="#d2d8d7", lw=.6)
        ax.tick_params(length=3)
    height.plot(ends, heights, "o-", lw=1, ms=2.8, color="#186966")
    height.set_ylabel(r"Line zero, $\mathrm{Im}\,s-T_D$")
    height.ticklabel_format(axis="y", style="plain", useOffset=False)
    slope.stairs(within, [start, *ends], baseline=None, color="#ab4f1e", lw=1.25,
                 label="Every integer cutoff in the block")
    slope.plot(ends, endpoint, "o", ms=2.8, color="#186966", label="Block endpoint")
    slope.axhline(0, color="#242c32", lw=.8, linestyle="--")
    slope.set_ylim(bottom=-8)
    slope.set_ylabel(r"Lower bound for $-\mathrm{Im}\,F_N'/S_0$")
    slope.set_xlabel(r"Included norm $N$ (millions)")
    slope.legend(loc="lower left", frameon=False, fontsize=9)
    fig.savefig(ROOT / "docs/figures/gaussian-intervening-slope.png", dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    main()
