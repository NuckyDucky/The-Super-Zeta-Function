"""Evaluate the two witnesses' arithmetic references at the first Riemann zero.

Run after flank_signature.py. The optional JSON input consists of outward-rounded
degree enclosures from that computation, not point-valued decimal angles.
"""
import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx


def reference(w, b):
    scale = (-w * arb.pi().log()).exp()
    return scale * (w.zeta(b) + w.zeta(1-b))


def reference_shift(angle):
    # Each real positive squared cosine spectrum is periodic in angle mod pi.
    b = (1-arb(2)*angle/180)/2
    if b > 1:
        b = b-1
    assert 0 < b < 1
    return b


def complex_ball(z):
    return {"re": z.real.str(29), "im": z.imag.str(29), "magnitude": abs(z).str(25)}


def run(signature):
    ctx.prec = 384
    pi = arb.pi()
    rho = acb.zeta_zero(1)
    scale = (-rho * pi.log()).exp()
    records, old_refs = {}, []
    for tag in ("left","right"):
        angle = arb(signature["flanks"][tag]["P"]["phase_degrees"])
        b0, b1 = reference_shift(angle), reference_shift(angle-30)
        old, new = reference(rho, b0), reference(rho, b1)
        assert not old.contains(0) and not new.contains(0)
        records[tag] = {"original_shift": b0.str(26), "clockwise_shift": b1.str(26),
                        "original": complex_ball(old), "clockwise": complex_ball(new)}
        old_refs.append(old)
    assert old_refs[0].overlaps(old_refs[1])

    # For the missing zero mode at -pi/2, let x be angle offset in radians.
    # After subtracting |x|^(-w), evaluate at b=1±x/pi to avoid cancellation.
    curvature_coeff = scale * rho * (rho+1) * (rho+2).zeta() / pi**2
    assert not curvature_coeff.contains(0)
    probe = arb(1)/10000
    h = probe / pi
    reg_value = scale * (rho.zeta(1+h)+rho.zeta(1-h))
    full_value = reference(rho,h)
    assert (full_value - reg_value).overlaps(acb(probe)**(-rho))
    assert not reg_value.contains(0)
    assert abs(reg_value/probe**2 - curvature_coeff) < arb(1)/100000
    return {"precision_bits":ctx.prec, "riemann_zero":complex_ball(rho), "flanks":records,
            "pivot_quadratic_coefficient":complex_ball(curvature_coeff),
            "angle_increment_radians":"1/10000",
            "regularized_value_after_offset":complex_ball(reg_value),
            "finite_difference_over_x_squared":complex_ball(reg_value/probe**2)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("signature", type=Path)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    result = json.dumps(run(json.loads(args.signature.read_text(encoding="utf8"))),indent=2)
    if args.output:
        args.output.write_text(result+"\n",encoding="utf8")
    print(result)
