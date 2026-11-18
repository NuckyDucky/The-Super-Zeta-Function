"""Uniform error of an exact finite regrouping of the native Mellin recursion."""
from fractions import Fraction
from pathlib import Path
import json
from flint import arb, ctx


def ball(rational):
    value = Fraction(rational)
    return arb(value.numerator)/value.denominator


def verify(k):
    ctx.prec = 192
    x,y=map(ball,("4.749479070945369e-8","0.509892982511772"))
    H = 2*k*arb.pi()/(160*((x/y)**2).log1p())
    g = (1/H).sin()**2/8
    expm2=arb(-2).exp()
    assert 3*expm2/(1-expm2)**2<1
    data=json.loads(Path(__file__).with_name(f"distance-h{k}.json").read_bytes())
    assert data["harmonic"] == k
    kappa=ball(data["distance_coefficient_s"])
    cases = [
        (21, 1, ("0.00174038", "0.00264469"), ("0.000482", "0.000563")),
        (7, 15, ("0.000077762", "0.000118312"), ("0.0000216", "0.0000252")),
        (21, 43, ("2.164e-58", "3.293e-58"), ("6.0e-59", "7.1e-59")),
    ]
    for blocks, tau, residual_caps, distance_caps in cases:
        assert 0 < tau/H < arb.pi()/2
        S = (tau/H).sin()
        assert S**2 > 2*g > 0
        q = g/(S**2-g)
        integral_bound = 2+(2*(2/S).log()+1)/S**2
        upper = 2*(tau*(H+ball("1/2"))/H).exp()*integral_bound*q**blocks/(arb.pi()*(H-ball("1/2")))
        assert upper < ball(residual_caps[k-2]) < ball("3/1000")
        assert upper/kappa < ball(distance_caps[k-2])
        print(f"H{k}, {blocks} blocks, tau={tau}: error <= {upper.upper().str(16)}, "
              f"distance <= {(upper/kappa).upper().str(16)}")


if __name__=="__main__":
    verify(2)
    verify(3)
