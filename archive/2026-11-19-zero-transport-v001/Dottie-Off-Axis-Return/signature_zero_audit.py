"""Independent checkpoint audit for the q=6 to q=4 continuations.

Uses the bare Hurwitz sum and Rouché's theorem on disks centered at the
published checkpoint midpoints. This verifies isolated simple zeros at
the checkpoints; the segmentwise connections are in arithmetic_braid.py.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def series(z, b):
    t = acb_series([z, 1], 2)
    return t.zeta(b) + t.zeta(1-b)


def audit(path):
    records = json.loads(path.read_text())["paths"]
    out = []
    for record in records:
        checkpoints = record["checkpoints"]
        upper = arb(0)
        radius = arb('1e-11')
        step = acb(arb(0, radius), arb(0, radius))
        for i, point in enumerate(checkpoints):
            q = Fraction(point["shift"])
            b = arb(q.numerator)/q.denominator
            box = acb(arb(point["zero"]["real"]), arb(point["zero"]["imag"]))
            center = box.mid()
            assert abs(box-center) < radius
            val = series(center, b)
            d = val[1].mid()
            # For |z-c|=r, compare H(z) with D(z-c).
            ratio = (abs(val[0])/radius + abs(series(center+step, b)[1]-d)) / abs(d)
            assert ratio < 1
            upper = max(upper, ratio.upper())
            if i in (0, len(checkpoints)-1):
                which = 'initial' if i == 0 else 'terminal'
                expr = record[which+'_root_expression']
                if 'Riemann' in expr:
                    idx = int(expr.split('#')[-1]) if '#' in expr else 1
                    known = acb.zeta_zero(idx)
                else:
                    multiple, modulus = int(expr.split('*')[0]), int(expr.split('(')[-1][:-1])
                    known = acb(0,multiple * arb.pi()/arb(modulus).log())
                    assert not known.zeta().contains(0)
                assert abs(known - center) < radius
        out.append(dict(path=path.name, source=record['initial_root_expression'],
                        terminal=record['terminal_root_expression'],
                        simple_zero_disks=len(checkpoints), disk_radius=radius.str(11),
                        largest_Rouche_ratio=upper.str(13)))
    return out


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('paths', nargs='+', type=Path)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    ctx.prec = 320
    ctx.cap = 2
    result = dict(precision=ctx.prec, checked=[rec for f in args.paths for rec in audit(f)])
    s = json.dumps(result, indent=2)
    print(s)
    if args.out:
        args.out.write_text(s+'\n')
