"""Generate the README figure using the midpoint profile. Requires matplotlib 3.11.2."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
from matplotlib import pyplot as plt
from matplotlib.ticker import MaxNLocator


def draw(directory):
    records = json.loads((directory / "compute/jets.json").read_bytes())
    rows = records["profiles"]
    events = [event["mid"] for event in records["events"]]
    passes = events[::2]
    colors = ("#006d76", "#aa482d", "#694497")
    fig, (plane, overlay) = plt.subplots(1, 2, figsize=(11.4, 4.2), layout="constrained")
    for ax in (plane, overlay):
        ax.spines[["top","right"]].set_visible(False)
        ax.grid(axis="y", color="#dae0df", lw=.7)
        ax.set_axisbelow(True)
        ax.yaxis.set_major_locator(MaxNLocator(5))
    plane.axhline(37.25, color="#515a60", lw=1, ls="--")
    plane.plot([r[1] for r in rows], [r[2] for r in rows], color="#344951", lw=1.9)
    for k, (event, color) in enumerate(zip(passes, colors), 1):
        plane.scatter(event["sigma"],event["T"],color=color,edgecolor="white",s=52,zorder=4)
        plane.annotate(str(k), (event["sigma"],event["T"]), xytext=(4,8), textcoords="offset points",
                       color=color, fontsize=12, weight="bold")
        nearby = [r for r in rows if abs(r[0]-event["alpha"]) <= .25]
        overlay.plot([r[0]-event["alpha"] for r in nearby], [r[2]-37.25 for r in nearby],
                     color=color, lw=2.4, label=f"Pass {k}")
    for event, text, offset in [(events[1], "crest", (-3,9)), (events[3], "trough", (3,-15))]:
        plane.scatter(event["sigma"],event["T"],color="#344951",marker="D",s=22)
        plane.annotate(text, (event["sigma"],event["T"]), xytext=offset,textcoords="offset points",fontsize=9)
    plane.set(xlabel="Real part of the moving zero",ylabel="Height T")
    plane.set_title("Three addresses at the same height", loc="left", pad=13)
    overlay.axhline(0, color="#515a60", lw=.8, ls="--")
    overlay.axvline(0, color="#515a60", lw=.8, ls=":")
    overlay.scatter([0], [0], color="#344951", s=23, zorder=4)
    overlay.legend(frameon=False, ncols=3, loc="upper center", fontsize=9)
    overlay.set_title("The passes aligned at their crossing", loc="left", pad=13)
    overlay.set(xlabel="Clockwise degrees from each crossing",ylabel="Height above 37.25",ylim=(-.071,.071))
    fig.savefig(directory / "preview.png", dpi=175, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    draw(Path(__file__).resolve().parent)
