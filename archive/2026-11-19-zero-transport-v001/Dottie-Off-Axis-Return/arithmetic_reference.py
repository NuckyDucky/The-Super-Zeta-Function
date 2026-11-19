"""Directed angular detachment of third-, fourth-, and sixth-residue references.
Usage: python arithmetic_reference.py [--output arithmetic_reference.json]
Requires python-flint 0.9.0. All angles and angle derivatives are in radians.
"""
import argparse
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx, dirichlet_char


def complex_record(z):
    return {"real": z.real.str(48), "imag": z.imag.str(48)}


def reference(w, b):
    return (w.zeta(b) + w.zeta(1 - b)) * (-w * arb.pi().log()).exp()


def derivative_w(w, b):
    variable = acb_series([w, 1], 2)
    return ((variable.zeta(b) + variable.zeta(1-b)) *
            (-variable * arb.pi().log()).exp())[1]


def derivative_angle(w, b):
    return w * ((w + 1).zeta(b) - (w + 1).zeta(1 - b)) * (
        -(w + 1) * arb.pi().log()).exp()


def disk_check(center, radius, b, correction=None):
    # The disk lies in this enclosing square. The complex Newton map
    # N(z)=z-R(z)/D is a contraction and takes the disk strictly inside itself.
    D = derivative_w(center, b.mid()).mid()
    square = center + acb(arb(0, radius), arb(0, radius))
    factor = abs(1-derivative_w(square, b)/D)
    shift = abs(reference(center, b)/D) if correction is None else correction / abs(D)
    return factor, shift, factor < 1 and shift + factor * radius < radius


def checked_root(rho, v, h, b0):
    b = b0 - h / arb.pi()
    # A common contracting Newton disk for every intermediate angle
    # joins the displaced root to the original one at h=0.
    b_hull = b0.union(b)
    base_center = rho.mid()
    base_error = abs(reference(base_center,b0))
    numerator = base_error + abs(h) * abs(derivative_angle(base_center,b_hull))
    tracking_radius = arb(1) / 1000
    all_q, all_shift, attached = disk_check(base_center, tracking_radius, b_hull, numerator)
    assert attached, (all_q, all_shift, tracking_radius)
    center = (rho + v * h).mid()
    for _ in range(5):
        center = (center - reference(center, b) / derivative_w(center, b)).mid()
    radius = arb(1) / 10**40
    q, shift, inside = disk_check(center, radius, b)
    assert inside and q.upper() < arb("1e-35"), (q, shift)
    zbox = center + acb(arb(0,radius), arb(0,radius))
    assert not zbox.real.contains(arb(1)/2)
    assert not zbox.zeta().contains(0)
    assert abs(center-base_center)+radius < tracking_radius
    return {"angular_step": h.str(12), "nearby_reference_zero": complex_record(zbox),
            "absolute_riemann_zeta_at_reference_zero": abs(zbox.zeta()).str(32),
            "reference_at_original_riemann_zero": complex_record(reference(rho, b)),
            "Newton_disk_radius": radius.str(16), "Newton_contraction_factor": q.str(16),
            "uniform_tracking_disk_radius":tracking_radius.str(16),
            "uniform_contraction_factor":all_q.str(16)}


def run():
    ctx.prec = 384
    ctx.cap = 3
    rho = acb.zeta_zero(1)
    zprime = acb_series([rho,1],2).zeta()[1]
    assert not zprime.contains(0)
    pi = arb.pi()
    angles = []
    for q,prime_divisors in [(3,(3,)),(4,(2,)),(6,(2,3))]:
        b0 = arb(1)/q
        char = dirichlet_char(q,q-1)
        L = char.l(rho+1)
        if q == 6:
            induced = (1+acb(2)**(-rho-1))*dirichlet_char(3,2).l(rho+1)
            assert L.overlaps(induced)
        slope = rho * acb(q/pi)**(rho+1) * L
        assert derivative_angle(rho,b0).overlaps(slope)
        assert derivative_angle(rho,1-b0).overlaps(-slope)
        w_deriv = acb(q/pi)**rho * zprime
        for prime in prime_divisors:
            w_deriv *= 1-acb(prime)**(-rho)
        assert w_deriv.overlaps(derivative_w(rho,b0))
        v = -slope/w_deriv
        assert not v.real.contains(0)
        assert reference(rho,b0).contains(0)
        h = -arb(1)/10**5
        examples = [checked_root(rho,v,h,b0), checked_root(rho,-v,h,1-b0)]
        angles.append({"q":q, "positive_anchor_degrees":90-180//q,
            "angular_reference_slope_at_positive_anchor":complex_record(slope),
            "moving_reference_zero_speed_per_radian_at_positive_anchor":complex_record(v),
            "positive_to_clockwise":examples[0], "negative_to_clockwise":examples[1]})
    return {"precision_bits":ctx.prec, "rho":complex_record(rho),
            "zeta_prime":complex_record(zprime),
            "anchors":angles}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    args = p.parse_args()
    result = json.dumps(run(), indent=2)
    if args.output:
        args.output.write_text(result+"\n",encoding="utf-8")
    print(result)
