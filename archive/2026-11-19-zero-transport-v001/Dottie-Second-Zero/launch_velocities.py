"""Directed starting velocities of four marked zeros at the sixty-degree anchor.

Run with Python 3 and python-flint 0.9.0.
    python launch_velocities.py --output launch_velocities.json

On the clockwise arc let u=pi/3-theta (radians), b=1/6+u/pi and
R=pi^(-w)[hurwitz(w,b)+hurwitz(w,1-b)]. At b=1/6,
    R=pi^(-w)(2^w-1)(3^w-1) zeta(w).
For w0=2*pi*i*k/log(p), {p,q}={2,3}, implicit differentiation gives
    dw/du=6*w0*q^w0*L(1+w0,chi6) /
        (pi*log(p)*(q^w0-1)*zeta(w0)).
The character chi6 is +1 at 1 and -1 at 5 modulo 6, zero elsewhere.
The second evaluation differentiates the two Hurwitz sums directly.
Every evaluation here takes place at the explicitly specified starting seed.
"""
import argparse
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx, dirichlet_char


def enclosure(z):
    return {"real": z.real.str(32), "imaginary": z.imag.str(32)}


def check(label, p, k):
    pi = arb.pi()
    b = arb(1)/6
    q = 6//p
    z = acb(0, 2*k*pi/arb(p).log())
    bscale = (-z*pi.log()).exp()
    var = acb_series([z,1],2)
    hurwitz_dw = ((var.zeta(b)+var.zeta(1-b))*(-var*pi.log()).exp())[1]
    hurwitz_du = -z*bscale*((z+1).zeta(b)-(z+1).zeta(1-b))/pi
    assert not hurwitz_dw.contains(0)
    from_hurwitz = -hurwitz_du/hurwitz_dw

    chi = dirichlet_char(6, 5)
    assert [chi(j) for j in range(6)] == [0,1,0,0,0,-1]
    qpow = acb(q)**z
    zeta = z.zeta()
    assert not (qpow-1).contains(0) and not zeta.contains(0)
    from_dirichlet = 6*z*qpow*chi.l(z+1) / (
        pi*arb(p).log()*(qpow-1)*zeta)
    assert from_hurwitz.overlaps(from_dirichlet)
    # Each real and imaginary enclosure separately certifies its sign.
    assert not from_dirichlet.real.contains(0) and not from_dirichlet.imag.contains(0)
    return {
        "role": label, "p":p, "k":k, "seed":f"{2*k}*pi*i/log({p})",
        "seed_enclosure":enclosure(z),
        "dirichlet_velocity_per_clockwise_radian":enclosure(from_dirichlet),
        "hurwitz_velocity_per_clockwise_radian":enclosure(from_hurwitz),
        "velocity_per_clockwise_degree":enclosure(from_dirichlet*pi/180),
        "horizontal_launch":"right" if from_dirichlet.real>0 else "left",
        "vertical_launch":"up" if from_dirichlet.imag>0 else "down",
    }


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    ctx.prec=320
    ctx.cap=3
    rows=[check(*seed) for seed in [
        ("previously followed",3,2), ("previously followed",3,3),
        ("prospective dyadic seed",2,2), ("prospective triadic seed",3,4)]]
    result={"bits":ctx.prec,"native_angle_degrees":60,
            "observable":"instantaneous velocity of a simple reference zero per clockwise angular displacement",
            "rows":rows}
    out=json.dumps(result,indent=2)
    if args.output:
        args.output.write_text(out+"\n",encoding="utf-8")
    print(out)
