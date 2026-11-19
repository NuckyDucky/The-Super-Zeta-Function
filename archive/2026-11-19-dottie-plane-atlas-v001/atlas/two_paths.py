"""Follow the sixth Hurwitz zero and a horizontal neighbor. Rebuild their figure."""
import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from flint import acb, arb, ctx
from gray_locus import direct


HERE = Path(__file__).resolve().parent
TROUGH_DEGREES = "13.4091736091859436753"
NUDGE = "1e-6"


def correct(guess, shift, level):
    point = guess
    for _ in range(5):
        value, derivative = direct(point, shift, 2).coeffs()
        point = (point - (value - level) / derivative).mid()
    assert abs(direct(point, shift, 1)[0] - level) < arb("1e-40")
    return point


def follow(steps):
    reference = json.loads((HERE / "plane_reference.json").read_bytes())["trough"]
    ctx.prec = 192
    start_angle = arb(TROUGH_DEGREES)
    assert arb(reference["alpha"]).contains(start_angle)
    first_shift = arb(1) / 6 + start_angle / 180
    seed = acb(arb(reference["sigma"]), arb(reference["T"])).mid()
    zero = correct(seed, first_shift, acb(0))
    offset = arb(NUDGE)
    neighbor = (zero + offset).mid()
    level = direct(neighbor, first_shift, 1)[0].mid()
    incoming = [complex(zero)]
    point = zero
    for k in range(1, 65):
        angle = start_angle + (12 - start_angle) * k / 64
        point = correct(point, arb(1) / 6 + angle / 180, acb(0))
        incoming.append(complex(point))
    readings = []
    for k in range(steps + 1):
        angle = start_angle + (15 - start_angle) * k / steps
        shift = arb(1) / 6 + angle / 180
        zero = correct(zero, shift, acb(0))
        neighbor = correct(neighbor, shift, level)
        # Subtract before converting to double; the separation is a millionth.
        delta = (neighbor - zero) / offset
        readings.append((float(angle), complex(zero), complex(neighbor), float(abs(delta))))
    assert abs(zero - acb.zeta_zero(6)) < arb("1e-40")
    return np.asarray(incoming[::-1]), readings


def draw(out):
    approach, fine = follow(320)
    _, coarse = follow(160)
    for a, b in zip(fine[::2], coarse, strict=True):
        assert all(abs(x-y) < 1e-13 for x, y in zip(a, b, strict=True))
    h, primary, nearby, gap = zip(*fine)
    h, gap = np.array(h), np.array(gap)
    primary, nearby = np.array(primary), np.array(nearby)
    peak = int(np.argmax(gap))
    assert abs(gap[0]-1) < 1e-12 and 1.233 < gap[peak] < 1.235 and .93909 < gap[-1] < .93910
    ink, teal, rust, grey = "#172f3a", "#14617a", "#b45323", "#687985"
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.labelcolor": ink, "text.color": ink,
                         "xtick.color": grey, "ytick.color": grey, "axes.edgecolor": "#a9b4b8"})
    fig = plt.figure(figsize=(12.2, 6.6), facecolor="white")
    fig.text(.065, .908, "Two nearby paths spread apart, then draw closer", size=23,
             weight="bold")
    fig.text(.065, .847, "At the last low point, start a second path one millionth of a unit to the right. Follow both through the same turn.", size=11.6)
    fig.text(.065, .731, "Where the paths travel", size=16, weight="bold")
    fig.text(.552, .731, "How far apart they are", size=16, weight="bold")
    fig.text(.065, .685, "Solid blue and dashed rust overlap at this scale.", color=grey, size=10.5)
    fig.text(.552, .685, "One unit on this ruler is the initial gap.", color=grey, size=10.5)
    left = fig.add_axes([.069, .242, .402, .37])
    left.set_aspect("equal", adjustable="box")
    left.plot(approach.real, approach.imag, color=grey, lw=2)
    left.plot(primary.real, primary.imag, color=teal, lw=3.8)
    left.plot(nearby.real, nearby.imag, color=rust, lw=1.45, dashes=(3, 3))
    left.plot(primary[0].real, primary[0].imag, "o", mfc="white", mec=ink, mew=1.6, ms=7)
    left.plot(primary[-1].real, primary[-1].imag, "*", color=teal, ms=13)
    left.annotate("Approach", (approach[14].real, approach[14].imag),
                  xytext=(0, 9), textcoords="offset points", ha="center", color=grey, fontsize=9)
    left.annotate("Trough", (primary[0].real, primary[0].imag),
                  xytext=(0, -15), textcoords="offset points", ha="center", weight="bold", fontsize=10)
    left.annotate("Sixth zero", (primary[-1].real, primary[-1].imag),
                  xytext=(-3, 10), textcoords="offset points", ha="right", weight="bold", fontsize=10)
    left.set(xlim=(-.51,.60), ylim=(37.11,37.68), xticks=[-.4,-.2,0,.2,.4,.6],
             yticks=[37.2,37.4,37.6], xlabel="Real part", ylabel="Height (imaginary part)")
    right = fig.add_axes([.565, .255, .371, .349])
    right.axhline(1, color="#97a5aa", lw=1.1, dashes=(3, 3))
    right.plot(h, gap, color=teal, lw=2.8)
    right.scatter([h[0],h[peak],h[-1]], [1,gap[peak],gap[-1]], color=teal, s=29, zorder=3)
    right.annotate("Start  1.000", (h[0], 1), xytext=(5, -17), textcoords="offset points", fontsize=9.5)
    right.annotate(f"Widest sampled gap  {gap[peak]:.3f}", (h[peak], gap[peak]), xytext=(0, 10),
                   ha="center", textcoords="offset points", weight="bold", fontsize=10)
    right.annotate(f"Finish  {gap[-1]:.3f}", (h[-1], gap[-1]), xytext=(-3, -16),
                   ha="right", textcoords="offset points", fontsize=9.5, weight="bold")
    right.set(xlim=(13.34, 15.07), ylim=(.88, 1.29), xticks=[13.5,14,14.5,15],
              yticks=[.9,1,1.1,1.2], xlabel="Clockwise turn (degrees)", ylabel="Gap / initial gap")
    for ax in (left, right):
        ax.grid(axis="y", color="#e0e6e8", lw=.7)
        ax.set_axisbelow(True)
    fig.text(.065,.102,"The trough is where the original path stops descending. It then rises to the sixth zero while its neighbor first drifts away,",size=10.9)
    fig.text(.065,.059,"then finishes 6.1% closer than it started. The curve on the right measures their separation at each angle.",size=10.9)
    fig.savefig(out / "two_paths.png", dpi=220)
    plt.close(fig)
    print(f"{len(fine)} samples; largest sampled gap {gap[peak]:.12g} at {h[peak]:.8f} degrees; final gap {gap[-1]:.12g} times initial")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    draw(args.output)
