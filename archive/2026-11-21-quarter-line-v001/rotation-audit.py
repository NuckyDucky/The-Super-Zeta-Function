"""Compare the local directions of increasing log modulus in the common w plane."""
from importlib import import_module
from pathlib import Path
import json

from flint import acb, arb, ctx, fmpq


def measure():
    ctx.prec = 256
    ratio = fmpq(4749479070945369, 10**23) / fmpq(509892982511772, 10**15)
    td = arb.pi() / (80 * arb(ratio**2).log1p())
    w0 = acb(arb(1)/2, td - arb(1)/512)
    logu = import_module("reflected-modulus-contrast").first_root().log()
    _, coeff, err = import_module("side-by-side").cauchy_interpolant(w0)
    step = arb(1)/64
    # All ordinary-zeta Cauchy circles about the three centers fit within
    # |w-w0|<=1/20, where the alias and Taylor truncation error is bounded.
    assert arb(1)/64 + step < arb(1)/20
    dp_err = err/step
    assert dp_err < arb("1e-15")
    eps_prime = arb(0, dp_err.upper())

    # Write Z(w/2) = u^(-w) (1+E(w)). Use the same Cauchy radius step
    # in the w plane for E at the three centers. All inputs s=w/2 stay
    # in the proved band, including the exterior of both measuring circles.
    height = (w0.imag + arb(0, step))/2
    sigma = (w0.real + arb(0, arb(1)/64 + step))/2
    assert sigma > fmpq(7,32) and sigma < fmpq(9,32) and height > 100
    logerr = (70*(height+2)).log() + (arb(11)/10-2*logu.imag)*height + 2*sigma*logu.real
    assert logerr < -155258110290 * arb(10).log()
    rel = arb("1e-56")
    assert logerr < rel.log()
    correction = rel / (step * (1-rel))
    assert correction < arb("1e-54")
    eps_c = arb(0, correction.upper())
    spectral_logderiv = -logu + acb(eps_c, eps_c)
    readings = []
    for name, offset in [("Left", -arb(1)/64), ("Middle", arb(0)), ("Right", arb(1)/64)]:
        # DFT coefficients use v=(w-w0)/r with r=1/10. Horner here gives
        # dp/dw, not dp/dv. Direct FLINT evaluation supplies the denominator.
        v = 10*offset
        dp = acb(0)
        for j in range(len(coeff)-1, 0, -1):
            dp = dp*v + 10*j*coeff[j]
        zeta = (w0+offset).zeta()
        assert abs(zeta) > 0
        ordinary_logderiv = (dp + acb(eps_prime,eps_prime))/zeta
        gz = spectral_logderiv.conjugate()
        gr = ordinary_logderiv.conjugate()
        assert abs(gr) > 0 and abs(gz) > 0
        turn = (gz/gr).arg()
        readings.append(dict(location=name, re_w=(w0.real+offset).str(16),
                   gradient_ordinary=gr.str(18), gradient_original=gz.str(18),
                   angle_ordinary_rad=gr.arg().str(16),angle_original_rad=gz.arg().str(16),
                   signed_rotation_ordinary_to_original_rad=turn.str(16),
                   signed_rotation_ordinary_to_original_degrees=(180*turn/arb.pi()).str(16),
                   slope_ordinary=abs(gr).str(16), slope_original=abs(gz).str(16),
                   slope_ratio_original_to_ordinary=(abs(gz)/abs(gr)).str(16)))
    return dict(observable="gradient of log modulus in the w=x+iy plane; represented by gx+i gy",
        direction="positive signed rotation is counterclockwise, from ordinary zeta to original Z",
        functions=["zeta(w)","Z(w/2;1)"], height=w0.imag.str(38), radius_in_w="1/64",
        ordinary_derivative_error_upper=dp_err.str(16), original_log_derivative_error_upper="1e-54",
        readings=readings)


def draw(result):
    from math import cos, sin, pi
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Arc, Circle
    from matplotlib.lines import Line2D

    fig, axes = plt.subplots(1,3,figsize=(9.7,3.65),layout="constrained")
    colors = ["#c05b25", "#0b7683"]
    for ax, row, address in zip(axes, result["readings"], ["31/64", "1/2", "33/64"]):
        a = float(arb(row["angle_ordinary_rad"]).mid())
        b = float(arb(row["angle_original_rad"]).mid())
        delta = float(arb(row["signed_rotation_ordinary_to_original_rad"]).mid())
        ax.add_patch(Circle((0,0),1,fill=False,color="#b7c4c9",lw=.9))
        ax.axhline(0,color="#ced6d8",lw=.8)
        ax.axvline(0,color="#ced6d8",lw=.8)
        for angle, color in zip([a,b],colors):
            ax.annotate("",xy=(cos(angle),sin(angle)),xytext=(0,0),
                        arrowprops=dict(arrowstyle="-|>",color=color,lw=2.8,
                                        mutation_scale=17,shrinkA=0,shrinkB=0))
        low, high = sorted([a, a+delta])
        ax.add_patch(Arc((0,0),.74,.74,theta1=180*low/pi,theta2=180*high/pi,color="#596c73"))
        ax.set_title(r"$\mathrm{Re}\,w="+address+"$",fontsize=13)
        ax.text(0,-1.18,f"{delta:+.4f} rad",ha="center",fontsize=12)
        ax.set_xlim(-1.15,1.15); ax.set_ylim(-1.25,1.13)
        ax.set_aspect("equal"); ax.axis("off")
    fig.legend([Line2D([],[],color=c,lw=3) for c in colors],
               [r"$\nabla\,\log|\zeta(w)|$", r"$\nabla\,\log|\mathcal{Z}(w/2;1)|$"],
               loc="outside lower center", ncol=2,frameon=False)
    fig.savefig(Path(__file__).with_suffix(".png"),dpi=185,bbox_inches="tight",pad_inches=.08)
    plt.close(fig)


if __name__ == "__main__":
    result = measure()
    Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    draw(result)
    for row in result["readings"]:
        print(row["location"], row["angle_ordinary_rad"], row["angle_original_rad"],
              row["signed_rotation_ordinary_to_original_rad"], row["slope_ratio_original_to_ordinary"])

