"""First critical level of the polynomial on the RHS of the original quartic."""
from fractions import Fraction
from math import comb
import json
from pathlib import Path

from flint import arb, ctx, fmpz_poly


def main():
    ctx.prec = 192
    coefficients = [1813853, 644010, -1810543, -1039740, 961000]
    p = fmpz_poly(coefficients)
    critical = p.derivative().complex_roots()
    roots = p.complex_roots()
    assert len(roots) == 4 and all(m == 1 for _, m in roots)
    assert len(critical) == 3 and all(m == 1 and z.imag == 0 for z, m in critical)
    rows = sorted([(p(z.real), z.real) for z, _ in critical], key=lambda row: float(row[0]))
    assert 0 < rows[0][0] < 6000 < rows[1][0] < rows[2][0]
    level, center = rows[0]
    assert p.derivative().derivative()(center) > 0

    # Identify both inverse sheets that meet at the first level.
    # On |z-7/5|=1/10 the quadratic Taylor term dominates everything
    # else for EVERY input value v with |v|<=6000, by Rouche.
    a, r = Fraction(7, 5), Fraction(1, 10)
    expansion = [sum(c*comb(k,j)*a**(k-j) for k,c in enumerate(coefficients) if k>=j)
                 for j in range(len(coefficients))]
    dominant = abs(expansion[2])*r**2
    rest = 6000 + sum(abs(c)*r**j for j,c in enumerate(expansion) if j!=2)
    assert dominant > rest
    disk_center = arb(7)/5
    assert abs(center-disk_center) < arb(1)/10
    pair = [z for z,_ in roots if abs(z-disk_center) < arb(1)/10]
    assert len(pair) == 2 and pair[0].overlaps(pair[1].conjugate())
    result = dict(precision_bits=ctx.prec, ascending_coefficients=coefficients,
                  critical_values=[dict(c=str(c),value=str(v)) for v,c in rows],
                  first_level=str(level), first_critical_input=str(center),
                  merging_roots=[dict(re=str(z.real), im=str(z.imag)) for z in pair],
                  rouche_circle="|z-7/5|=1/10", output_disk="|v|<=6000",
                  dominant_term=str(dominant), bound_for_rest=str(rest))
    path = Path(__file__).with_name("quartic-first-tube.json")
    path.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(level, center)


if __name__ == "__main__":
    main()
