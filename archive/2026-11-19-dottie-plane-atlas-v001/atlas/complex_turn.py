"""Draw actual continued paths and their relative displacement in the complex plane."""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from plane_map import HERE, fields, rk
from two_paths import follow


INK = "#183342"
SLATE = "#52666e"
TEAL = "#006a78"
ROW_COLORS = ("#a85017", "#187c79", "#7863a4", "#5b748a")


def arrow(ax, path, i, j, color, size=12):
    a, b = path[i], path[j]
    ax.annotate("", xy=(b.real, b.imag), xytext=(a.real, a.imag),
                arrowprops=dict(arrowstyle="-|>", mutation_scale=size,
                                shrinkA=0, shrinkB=0, color=color, linewidth=.95))


def setup(ax):
    ax.set_aspect("equal", adjustable="box")
    ax.spines[["top", "right"]].set_visible(False)
    ax.spines[["bottom", "left"]].set_color("#a2b1b7")
    ax.grid(color="#e5eaec", linewidth=.65)
    ax.set_axisbelow(True)


def field_map(out, zero, h0):
    with np.load(HERE / "plane_map.npz", allow_pickle=False) as data:
        cols, rows = [12, 44, 76, 108], [8, 32, 56, 80]
        x, y = data["x"][cols], data["y"][rows]
        indices = np.ix_(rows, cols)
        assert data["accepted"][indices].all()
        expected = data["end"][indices].flatten()
    starts = (x[None, :] + 1j*y[:, None]).flatten()
    fine, slope = rk(starts, h0, 384)
    coarse, _ = rk(starts, h0, 192)
    assert np.all(slope > 1e-4) and np.max(abs(fine[::2] - coarse)) < 2e-5
    assert np.max(abs(fine[-1] - expected)) < 2e-5
    levels = fields(starts, 1/6 + h0/180)[0]
    for angle, points in zip(np.linspace(h0, 15, len(fine)), fine):
        values = fields(points, 1/6 + angle/180)[0]
        assert np.all(abs(values-levels)/(1+abs(levels)) < 5e-7)

    fig = plt.figure(figsize=(9.7, 7.6), facecolor="white")
    fig.text(.07, .92, "Where do the starting points go?", fontsize=22, weight="bold")
    fig.text(.07, .864, "The sixth Hurwitz turn, drawn in the complex plane from 13.409° to 15° clockwise.", fontsize=11.4)
    ax = fig.add_axes([.074, .14, .56, .657])
    setup(ax)
    for k, path in enumerate(fine.T):
        color = ROW_COLORS[k // len(x)]
        ax.plot(path.real, path.imag, lw=1.15, color=color)
        arrow(ax, path, 128, 151, color, 9)
        ax.plot(path[0].real, path[0].imag, "o", mec=color, mfc="white", mew=1.4, ms=5.1)
        ax.plot(path[-1].real, path[-1].imag, "D", mec=color, mfc=color, ms=3.6)
    ax.plot(zero.real, zero.imag, color="white", lw=4.1, zorder=5)
    ax.plot(zero.real, zero.imag, color=INK, lw=2.3, zorder=6)
    ax.plot(zero[0].real, zero[0].imag, "o", mec=INK, mfc="white", mew=1.6, ms=7, zorder=7)
    ax.plot(zero[-1].real, zero[-1].imag, "*", mec="white", mfc=INK, mew=.65, ms=15, zorder=7)
    for name, z, delta, align in (("Trough",zero[0],(-12,5),"right"),
                                 ("Sixth zero",zero[-1],(2,-18),"center")):
        ax.annotate(name, (z.real,z.imag), xytext=delta, textcoords="offset points",
                    weight="bold", fontsize=9.5, ha=align, zorder=8,
                    bbox=dict(boxstyle="round,pad=.12", fc="white", ec="none", alpha=.92),
                    arrowprops=dict(arrowstyle="-",color=INK,lw=.6,shrinkA=0,shrinkB=5))
    ax.set(xlim=(-.73,1.07), ylim=(36.34,38.55), xticks=[-.5,0,.5,1],
           yticks=[36.5,37,37.5,38,38.5], xlabel="Real part of w", ylabel="Imaginary part of w")
    side=fig.add_axes([.64,.20,.33,.60]); side.axis("off")
    side.text(0,.95,"Follow one point",weight="bold",fontsize=14)
    for yy, marker, label, fill in ((.85,"o","Starting position","white"),(.76,"D","Final position",SLATE)):
        side.plot(.025,yy,marker,ms=6,mec=SLATE,mfc=fill,mew=1.3,transform=side.transAxes)
        side.text(.095,yy,label,va="center",transform=side.transAxes)
    side.text(0,.64,"Color gives the starting height",size=10.7,weight="bold")
    for n, (height, color) in enumerate(zip(y,ROW_COLORS)):
        yy=.55-.068*n
        side.plot([0,.09],[yy,yy],color=color,lw=2,transform=side.transAxes)
        side.text(.135,yy,f"{height:.2f}",va="center",size=10.3,transform=side.transAxes)
    side.text(0,.23,"The dark path",size=10.7,weight="bold")
    side.text(0,.17,"At the trough its height turns upward.\nThis path keeps the Hurwitz sum at zero\nand ends at the sixth Riemann zero.",fontsize=9.8,linespacing=1.55,va="top")
    side.set(xlim=(0,1),ylim=(0,1))
    fig.text(.07,.055,"Each colored path keeps its own starting value of the Hurwitz sum. A crossing on the page can occur at different turn angles.",size=9.1,color=SLATE)
    fig.savefig(out / "complex_turn.png", dpi=220)
    plt.close(fig)


def relative_map(out, angles, delta):
    fig = plt.figure(figsize=(8.6, 7.25), facecolor="white")
    fig.text(.075,.913,"Which way does the neighbor turn?",size=21,weight="bold")
    fig.text(.075,.858,"Keep the original moving point at the origin. One axis unit here equals the initial gap of one millionth.",size=10.8)
    ax=fig.add_axes([.09,.188,.85,.584])
    setup(ax)
    ax.axhline(0,color="#8a999e",lw=.9); ax.axvline(0,color="#8a999e",lw=.9)
    theta=np.linspace(-.1,1.75,240)
    ax.plot(np.cos(theta),np.sin(theta),color="#82939b",linestyle=(0,(3,3)),lw=1.1)
    ax.plot(delta.real,delta.imag,color=TEAL,lw=2.8)
    arrow(ax,delta,48,62,TEAL);arrow(ax,delta,227,240,TEAL)
    ax.scatter([0],[0],s=30,color=INK,zorder=4)
    ax.annotate("Original point", (0,0), xytext=(6,9),textcoords="offset points",size=9.6)
    ax.plot([0,delta[-1].real],[0,delta[-1].imag],color="#9eabae",lw=1)
    picks = [(0,"Start",(0,-20),"center"),(np.abs(angles-14.30).argmin(),"14.30°",(9,3),"left"),
             (-1,"Finish",(0,-19),"left")]
    for j,label,offset,align in picks:
        z=delta[j]
        ax.plot(z.real,z.imag,"o",mec=TEAL,mfc="white" if j==0 else TEAL,ms=6,zorder=5)
        ax.annotate(label,(z.real,z.imag),xytext=offset,textcoords="offset points",
                    fontsize=10.3,weight="bold",ha=align)
    ax.set(xlim=(-.16,1.30),ylim=(-.125,1.12),xticks=[0,.25,.5,.75,1,1.25],
           yticks=[0,.25,.5,.75,1], xlabel="Horizontal offset from the moving point",ylabel="Vertical offset")
    fig.text(.075,.091,"The dashed arc is one initial gap from the origin. Outside it, the pair is farther apart than at launch.",size=10.5)
    fig.text(.075,.049,"Final offset: 0.247 millionths right, 0.906 millionths up. Its direction has turned 74.74°.",size=10.5,weight="bold")
    fig.savefig(out / "complex_offset.png",dpi=220)
    plt.close(fig)


def draw(out):
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":11,"text.color":INK,
                         "axes.labelcolor":INK,"xtick.color":SLATE,"ytick.color":SLATE})
    _, records = follow(320)
    angles, zero, neighbor, gap = (np.asarray(column) for column in zip(*records))
    delta = (neighbor-zero)*1e6
    # Double rounding of the large common height can affect individual
    # components by <1e-8 on this magnified scale. follow() computed the
    # magnitude directly from a 192-bit difference before rounding.
    assert np.max(abs(abs(delta)-gap)) < 1e-8
    assert abs(delta[0]-1)<1e-8 and abs(delta[-1]-(.247208976+.905975071j))<1e-8
    field_map(out, zero, angles[0])
    relative_map(out, angles, delta)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=HERE)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    draw(args.output)
