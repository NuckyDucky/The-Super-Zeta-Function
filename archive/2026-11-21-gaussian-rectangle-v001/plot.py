"""Plot the regions and root brackets from certificate.json."""

import json
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import Circle


HERE = Path(__file__).resolve().parent


def main():
    record = json.loads((HERE / "certificate.json").read_text(encoding="utf-8"))
    augmented = record["augmented_infinite_model"]
    root_offset = sum(map(float, augmented["height_offset_bracket"])) / 2
    cream, ink = "#faf9f5", "#142b36"
    fig, (region, motion) = plt.subplots(1, 2, figsize=(10, 3.65),
                                         gridspec_kw={"width_ratios": [1.12, 1]},
                                         layout="constrained")
    fig.patch.set_facecolor(cream)
    for ax in (region, motion):
        ax.set_facecolor(cream)
        ax.tick_params(colors=ink, labelsize=9)

    region.axvspan(-63, 0, color="#d4e9e4")
    region.axvspan(0, 63, color="#f0dccb")
    for center in (-32, 32):
        region.add_patch(Circle((center, -4), 31, fill=False, edgecolor=ink,
                                linewidth=1, linestyle="--"))
    region.axvline(0, color=ink, linewidth=1)
    region.scatter([0], [root_offset * 2048], marker="*", color=ink, s=105, zorder=3)
    region.text(-32, -4, r"$\Im H>0$", ha="center", va="center", color=ink)
    region.text(32, -4, r"$\Im H<0$", ha="center", va="center", color=ink)
    region.set(xlim=(-63, 63), ylim=(-35, 27), xticks=[-63, -32, 0, 32, 63],
               yticks=[-35, -4, 27], xlabel=r"$2048\,(\Re w-1/2)$",
               ylabel=r"$2048\,(\Im w-T_D)$", aspect="equal")
    region.set_title("The two measuring disks", loc="left", color=ink, fontweight="bold")

    ys = [sum(map(float, row["height_offset_bracket"])) * 500 for row in record["prefix_boxes"]]
    xs = list(range(len(ys)))
    motion.plot(xs, ys, color="#38726e", lw=1.4, marker="o", markersize=4)
    motion.set(xlim=(-.45, 16.45), xticks=[0, 4, 8, 12, 16],
               xlabel=r"Block endpoint $k$   ($j=276824064+k\,2^{20}$)",
               ylabel=r"$1000\,(\Im w_j-T_D)$")
    motion.grid(axis="y", color="#c9cfd1", linewidth=.55)
    motion.spines[["top", "right"]].set_visible(False)
    motion.set_title("One line zero per prefix", loc="left", color=ink, fontweight="bold")

    fig.savefig(HERE / "rectangle.png", dpi=180)


if __name__ == "__main__":
    main()
