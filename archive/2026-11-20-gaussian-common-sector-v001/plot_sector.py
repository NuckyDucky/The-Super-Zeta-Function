"""Plot the angular spread of 193 readings sampled around the Gaussian circle."""
from math import pi
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from verify_sector import load_models, phase


def main():
    _, models = load_models()
    x, widths = [], []
    for j in range(1025):
        theta = phase.TAU * j / 1024
        anchor = models[0](theta)
        angles = [0.] + [float((model(theta) / anchor).arg().mid()) for model in models[1:]]
        widths.append(max(angles) - min(angles))
        x.append(float(theta.mid()))
    fig, ax = plt.subplots(figsize=(7.4, 3.5), layout="constrained")
    fig.patch.set_facecolor("#faf8f2")
    ax.set_facecolor("#faf8f2")
    ax.axhline(pi, color="#963c24", linestyle="--", linewidth=1.6)
    ax.plot(x, widths, color="#00746d", linewidth=2.2)
    ax.scatter([x[537]], [widths[537]], color="#00746d", s=24, zorder=3)
    ax.set(xlim=(0, 2*pi), ylim=(0, pi+.23), xlabel=r"$\theta$ (rad)",
           ylabel=r"Sector width $W(\theta)$ (rad)")
    ax.set_xticks([0, pi/2, pi, 3*pi/2, 2*pi],
                  ["0", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
    ax.set_yticks([0, 1, 2, pi], ["0", "1", "2", r"$\pi$"])
    ax.spines[["right", "top"]].set_visible(False)
    fig.savefig(Path(__file__).with_name("sector-width.png"), dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    main()
