"""Recover the two solutions to P(z)=v using only P on the circle |z-1.4|=0.1."""
from math import comb
from pathlib import Path
import json

from flint import arb, ctx, fmpz_poly

HERE = Path(__file__).resolve().parent


def moments(P, v):
    # z=b+d*t; use the Laurent coefficients on |t|=1.
    b, d = arb(7)/5, arb(1)/10
    cfs = [d**j * sum(arb(int(P[k]))*comb(k,j)*b**(k-j)
                       for k in range(j,5)) for j in range(5)]
    cfs[0] -= v
    u = {j-2:cfs[j]/cfs[2] for j in (0,1,3,4)}
    eta = sum(abs(h) for h in u.values()).upper()
    assert eta < arb(2)/5  # Two solutions, counting multiplicity, by Rouche.
    degree = 100
    tail = eta**(degree+1)/((degree+1)*(1-eta))
    power = {0:arb(1)}
    log_coeff = {k:arb(0) for k in (-1,-2)}
    for j in range(1,degree+1):
        product = {}
        for i, coeff in power.items():
            for h, add in u.items():
                product[i+h] = product.get(i+h,0) + coeff*add
        power = product
        for k in log_coeff:
            log_coeff[k] += (-1)**(j+1)*power.get(k,0)/j
    s1, s2 = [-k*(log_coeff[-k]+arb(0,tail.upper())) for k in (1,2)]
    mid = b+d*s1/2
    gap2 = d**2*(2*s2-s1**2)
    return mid, gap2


def main():
    ctx.prec = 192
    src = json.loads((HERE/"quartic-first-tube.json").read_text())
    P = fmpz_poly(src["ascending_coefficients"])
    c = arb(src["first_critical_input"])
    level = P(c)
    data = {}
    for label,v in (("0",arb(0)),("0.75",3*level/4),("1",level),("1.25",5*level/4)):
        mid, gap2 = moments(P,v)
        if label=="1":
            assert gap2.contains(0) and mid.overlaps(c)
        else:
            assert (gap2 > 0 if label=="1.25" else gap2 < 0)
        data[label] = dict(midpoint=str(mid), signed_squared_separation=str(gap2))
    center, g2 = moments(P,arb(0))
    y2 = -g2/4
    # Divide the monic real quadratic of the near roots into P, at the level
    # of its leading three coefficients to evaluate the other factor at c.
    k2 = arb(int(P[4]))
    k1 = arb(int(P[3])) + 2*center*k2
    k0 = arb(int(P[2])) + 2*center*k1 - (center**2+y2)*k2
    K = k2*c**2 + k1*c + k0
    offset = 2*(c-center)**2
    assert (2*level/K-offset).overlaps(2*y2)
    rec = dict(precision_bits=192, circle="|z-7/5|=1/10", series_degree=100,
               r_star=str(level), c=str(c), cases=data,
               neck_width_at_1_25=str(arb(data["1.25"]["signed_squared_separation"]).sqrt()),
               y=str(y2.sqrt()), other_factor_at_contact=str(K),
               uncorrected_spread=str(2*level/K), center_offset_correction=str(offset),
               corrected_spread=str(2*y2), quadratic_coefficient=str(P.derivative().derivative()(c)/2))
    (HERE/"quartic-neck.json").write_text(json.dumps(rec,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(rec,indent=2))


if __name__ == "__main__":
    main()
