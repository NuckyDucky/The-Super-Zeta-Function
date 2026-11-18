"""Directed local directions from the completed Riemann function at 2*T_D.

The probe uses the old upper bracket only. The saved second-harmonic line
bracket is read after producing the Newton iterates, solely for comparison.
Heights are formed with Arb, retaining sub-unit differences at 9e12.
"""
import json
from fractions import Fraction
from pathlib import Path

from dottie_grid_nomination import centers, rat
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent


def step(center, offset):
    w = acb(rat("1/2"), center) + offset
    value = w.zeta()
    h = arb(2)**-84
    radius = rat("1/4")
    assert w.real > radius and w.real < 1 and w.imag > 10
    # On the radius-1/4 disk the one-term Euler--Maclaurin estimate used by
    # offcenter_superzeta.interpolant is bounded by (Im(w)+3)^2.
    # Cauchy's bounds on the odd Taylor coefficients starting with degree 3.
    error = (w.imag+3)**2 * h**2 / (radius**3 * (1-(h/radius)**2))
    zprime = ((w+h).zeta()-(w-h).zeta())/(2*h)
    zprime += acb(arb(0,error),arb(0,error))
    gamma_term = 1/w + 1/(w-1) - arb.pi().log()/2 + (w/2).digamma()/2
    return -value/(zprime + gamma_term*value)


def upper_bracket(name, second=False):
    record = json.loads((HERE/name).read_bytes())
    data = record["count"] if second else record["arms"]["dottie"]
    lower, upper = map(Fraction, data["broad"]["line_brackets"][-1])
    return lower, upper


def bearing(v):
    return 180*v.arg()/arb.pi()


if __name__ == "__main__":
    ctx.prec = 320
    _, period, _, _ = centers()
    lo, hi = upper_bracket("dottie-grid-certificate.json")
    origin = 2*period+rat((lo+hi)/2)
    p0 = acb(rat("1/512"))
    offset = p0
    for j in range(3):
        correction = step(origin,offset)
        if j == 0:
            first = correction
            print("First predicted bearing, degrees", bearing(first).str(23))
            print("First predicted step (dx, dy)", first.str(23))
        offset = (offset+correction).mid()
        print("After step", j+1, "local coordinates", offset.str(26))
    lower, upper = upper_bracket("dottie-second-harmonic-count.json", second=True)
    target = acb(0,rat(lower).union(rat(upper))-rat((lo+hi)/2))
    print("Bracketed target minus probe", (target-p0).str(20))
    print("Bracketed bearing, degrees", bearing(target-p0).str(14))
    print("First angular error, degrees", abs(bearing(target-p0)-bearing(first)).str(10))
    print("Miss after one step", abs(target-(p0+first)).str(12))
    print("Last height belongs to independent bracket", target.imag.contains(offset.imag))
    assert target.imag.contains(offset.imag)
