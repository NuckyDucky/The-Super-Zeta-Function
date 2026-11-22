"""Map Z(w/2;1) and ordinary zeta(w) over the same two Dottie measuring disks.

Run with Python 3, python-flint 0.9.0, NumPy, and Matplotlib. This calculation
uses the root enclosure from reflected-modulus-contrast.py. The numerical data
for ordinary zeta come from FLINT's zeta evaluator at the actual height.
"""
from importlib import import_module
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq
import numpy as np


N = 64
SCALE = 2048
XMAX, YMAX = 72, 40                 # ticks are in 1/2048 input-plane units
OUT = Path(__file__).resolve().parent


def cauchy_interpolant(w0):
    sample_radius, majorant_radius, extent = arb(1)/10, arb(3)/10, arb(1)/20
    assert acb(arb(XMAX)/SCALE, arb(YMAX)/SCALE).abs_upper() < extent
    # On |w-w0|=3/10, Re w >= 1/5. The floor-integral identity bounds
    # |zeta(w)| <= |w/(w-1)|+|w|/Re(w). The same inequality holds inside.
    assert w0.real == arb(1)/2 and fmpq(1,2)-fmpq(3,10) == fmpq(1,5)
    assert w0.imag - majorant_radius > 1
    z_bound = arb(2) + 5*(w0.abs_upper() + majorant_radius)
    assert z_bound < 3 * 10**13
    unit_roots = [acb(0, 2*arb.pi()*k/N).exp() for k in range(N)]
    samples = [(w0 + sample_radius * root).zeta() for root in unit_roots]
    # Coefficients multiply ((w-w0)/sample_radius)^j. Positive Fourier
    # aliases at j+N,j+2N,... are explicitly included in the uniform error.
    coeff = [sum((samples[k] * unit_roots[(-k*j) % N] for k in range(N)), acb(0))/N
             for j in range(N)]
    x = extent / majorant_radius
    q = sample_radius / majorant_radius
    error = z_bound / (1-x) * (x**N + q**N/(1-q**N))
    assert error < arb("1e-16")
    eps = arb(0, error.upper())
    def evaluate(offset):
        point = offset / sample_radius
        p = acb(0)
        for c in reversed(coeff):
            p = p * point + c
        return p + acb(eps, eps)
    return evaluate, coeff, error


def calculate():
    ctx.prec = 288
    ratio = fmpq(4749479070945369, 10**23)/fmpq(509892982511772, 10**15)
    td = arb.pi() / (80*arb(ratio**2).log1p())
    w0 = acb(arb(1)/2, td-arb(1)/512)
    root = import_module("reflected-modulus-contrast").first_root()
    logu = root.log()
    # Each displayed w lies within the scope of band_absolute_error at s=w/2.
    height = (w0.imag + arb(0, arb(YMAX)/SCALE))/2
    sigma = (w0.real + arb(0, arb(XMAX)/SCALE))/2
    assert sigma > fmpq(7,32) and sigma < fmpq(9,32) and height > 100
    rel_log = (70*(height+2)).log()+(arb(11)/10-2*logu.imag)*height+2*sigma*logu.real
    assert rel_log < -155258110290 * arb(10).log()
    ell0 = -w0 * logu
    exponent = int((ell0.real/arb(10).log()).floor().unique_fmpz())
    scaled_center = acb(ell0.real-exponent*arb(10).log(), ell0.imag).exp()
    # Bound the true value after scaling on the complete window. Tiny error
    # is conservatively enlarged for display instead of pretending it is zero.
    leading_scaled_max = abs(scaled_center)*(arb(1)/20*abs(logu)).exp()
    assert leading_scaled_max < 10
    eps = arb(0, arb("1e-48"))
    def spectral(offset):
        return scaled_center * (-offset*logu).exp() + acb(eps, eps)

    ordinary, coeff, cauchy_error = cauchy_interpolant(w0)
    checks = {}
    for name,x,y in [("middle_of_window",0,0),("left_west",-63,0),("left_center",-32,0),
                     ("left_east",-1,0),("right_west",1,0),("right_center",32,0),
                     ("right_east",63,0),("right_north",32,31),("left_south",-32,-31)]:
        d = acb(arb(x)/SCALE, arb(y)/SCALE)
        direct_zeta = (w0+d).zeta()
        interpolation = ordinary(d)
        assert interpolation.contains(direct_zeta)
        z_ball = spectral(d)
        checks[name] = dict(x=x, y=y, zeta=direct_zeta.str(20),
                            zeta_abs=abs(direct_zeta).str(20), zeta_arg_rad=direct_zeta.arg().str(20),
                            scaled_super_zeta=z_ball.str(20), scaled_super_abs=abs(z_ball).str(20),
                            super_arg_rad=z_ball.arg().str(20))
    # Cover a full rectangle by complex interval evaluation of every 2x2
    # cell; in particular a branch cut cannot create a spurious color jump.
    residual_lower = arb(100)
    for x in range(-XMAX+1,XMAX,2):
        for y in range(-YMAX+1,YMAX,2):
            d = acb(arb(x,1)/SCALE, arb(y,1)/SCALE)
            ordinary_cell, super_cell = ordinary(d), spectral(d)
            assert ordinary_cell.real > 0 and super_cell.real < 0 and super_cell.imag < 0
            a, b = abs(ordinary_cell), abs(super_cell)
            assert a > arb("0.25") and b > arb(3)
            w = w0 + d
            prefactor = 2 * acb(arb.pi())**(-w) * (acb(2)**w - 1)
            cell_lower = (abs(prefactor) * a).lower()
            if cell_lower < residual_lower:
                residual_lower = cell_lower
    residual_millis = int((residual_lower * 1000).floor().unique_fmpz())
    assert residual_millis >= 1171 and residual_lower > arb(residual_millis) / 1000
    units = "1/2048 of a w-coordinate unit"
    data = dict(field="w = 1/2 + i(T_D-1/512) + (x+iy)/2048",
                domain=dict(horizontal=[-XMAX,XMAX],vertical=[-YMAX,YMAX],units=units),
                circle_centers=[[-32,0],[32,0]], circle_radii=dict(inner=30,outer=31),
                height=w0.imag.str(40), left_plot_scaling_power_of_ten=exponent,
                compared_functions=["original Z(w/2;1)","ordinary zeta(w)"],
                spectral_relative_error_less_than="10^(-155258110290)",
                zeta_cauchy=dict(samples=N,sample_radius="1/10",majorant_radius="3/10",
                      evaluation_radius="1/20",absolute_truncation_and_alias_error=cauchy_error.str(12)),
                whole_rectangle=dict(cells=2*XMAX//2*(2*YMAX//2), cell_dimensions=[2,2],
                        ordinary_abs_lower="0.25", scaled_super_abs_lower="3",
                        abs_super_zeta_minus_mellin_correction_lower=f"{residual_millis}/1000",
                        ordinary_real="positive",scaled_super_real_and_imag="both negative"),
                direct_arb_checks=checks)
    return data, scaled_center, logu, coeff


def make_figure(data, scaled_center, logu, coeff):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.patheffects as pe
    from matplotlib.ticker import MaxNLocator
    from matplotlib.patches import Circle
    def midpoint(z):
        return complex(float(z.real.mid()),float(z.imag.mid()))
    x, y = np.linspace(-XMAX,XMAX,361), np.linspace(-YMAX,YMAX,201)
    xx, yy = np.meshgrid(x,y)
    offset = (xx+1j*yy)/SCALE
    z = midpoint(scaled_center)*np.exp(-offset*midpoint(logu))
    ordinary = np.polynomial.polynomial.polyval(10*offset, [midpoint(c) for c in coeff])
    fig, axes = plt.subplots(2,2, figsize=(11.7,7.3), sharex=True, sharey=True,
                             layout="constrained")
    expn = data["left_plot_scaling_power_of_ten"]
    names = [r"$\mathcal{Z}(w/2;1)$",r"$\zeta(w)$"]
    for col, values in enumerate([z,ordinary]):
        axes[0,col].set_title(names[col],fontsize=19,pad=9)
        for row, vals in enumerate([abs(values),np.angle(values)]):
            ax = axes[row,col]
            pal = "viridis" if row == 0 else "cividis"
            image = ax.pcolormesh(x,y,vals,cmap=pal,shading="auto",rasterized=True)
            for c in [-32,32]:
                # White/black strokes make both annulus edges visible across colors.
                for rad,ls in [(31,"-"),(30,(0,(2,3)))]:
                    circle = Circle((c,0),rad,fill=False,ec="white",lw=0.9,ls=ls)
                    circle.set_path_effects([pe.withStroke(linewidth=1.8,foreground="#19292e")])
                    ax.add_patch(circle)
                mark, = ax.plot(c,0,'+',c='white',ms=8,mew=1.3)
                mark.set_path_effects([pe.withStroke(linewidth=2.7,foreground="#19292e")])
            ax.axvline(0,c="#17252c",lw=1,ls=(0,(1,2)))
            bar = fig.colorbar(image,ax=ax,location="right",shrink=.86,pad=.02)
            bar.ax.yaxis.set_major_locator(MaxNLocator(5))
            if row == 0 and col == 0:
                title = r"$|\mathcal{Z}|\,/\,10^{"+str(expn)+"}$"
            elif row == 0:
                title = r"$|\zeta|$"
            else:
                title = r"$\arg$ (rad)"
            bar.set_label(title)
            ax.set_aspect("equal")
            ax.set_xticks([-64,-32,0,32,64])
            ax.set_yticks([-32,0,32])
            ax.tick_params(length=3)
    for ax in axes[-1]:
        ax.set_xlabel(r"$2048\,(\mathrm{Re}\,w-1/2)$")
    for ax in axes[:,0]:
        ax.set_ylabel(r"$2048\,(\mathrm{Im}\,w-T_0)$")
    fig.savefig(OUT/"side-by-side.png",dpi=190,bbox_inches="tight",pad_inches=.08)
    plt.close(fig)


if __name__ == "__main__":
    record, scaled_center, logu, coeff = calculate()
    (OUT/"side-by-side.json").write_text(json.dumps(record,indent=2)+"\n", encoding="utf8")
    make_figure(record, scaled_center, logu, coeff)
    print("Checked all four panel fields, the full rectangle, and nine direct zeta evaluations.")

