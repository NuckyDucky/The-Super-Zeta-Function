"""Uniform image disks around 0 for the completed untwisted Hecke function.

See gaussian-strip-image.md for the maximum-modulus proof. Same positive
normalization as gaussian-loop-arcs.json. The result includes both
unresolved horizontal passages without filling them in with guessed points.
"""
import json
from pathlib import Path

from flint import acb, arb, ctx, dirichlet_char
from gaussian_inputs import height
from gaussian_inputs import Q


def main():
    ctx.prec = 192
    t, h = height(), arb(1)/16
    logb = (arb(Q).sqrt()/(2*arb.pi())).log()
    scale = 2*logb + acb(2,t).lgamma().real
    rows = []
    for p,q in ((9,8),(45,44)):
        r = arb(p)/q
        a = r-arb(1)/2
        zeta_k = acb(r).zeta()*acb(r).dirichlet_l(dirichlet_char(4,3))
        assert zeta_k.imag.contains(0) and zeta_k.real > 0
        # Minimize lambda*(a^2+h^2)+pi^2/(16 lambda) over all positive lambda.
        optimized_exponent = arb.pi()*(a*a+h*h).sqrt()/2
        log_radius = (r*logb + acb(r,t).lgamma().real - scale
                      + zeta_k.real.log() + optimized_exponent)
        radius = log_radius.exp()
        rows.append(dict(right_real_part=f"{p}/{q}",left_real_part=f"{q-p}/{q}",
                         zeta_Q_i=str(zeta_k.real), log_radius=str(log_radius),
                         radius_upper=str(radius.upper())))
    output=dict(precision_bits=ctx.prec, height=str(t), height_offsets=["-1/16","+1/16"],
                compact_domain="All real parts and imaginary parts in each closed rectangle",
                normalized_output="H(w) / |B^(2+iT_D) Gamma(2+iT_D)|",
                center_of_disk=[0,0], uniform_image_bounds=rows)
    out=Path(__file__).with_name("gaussian-strip-image.json")
    out.write_text(json.dumps(output,indent=2)+"\n",encoding="utf8")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
