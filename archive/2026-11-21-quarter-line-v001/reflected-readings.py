"""Evaluate Z-J through its exact Riemann factorization at three common-height inputs."""
from pathlib import Path
import json
from flint import arb, acb, ctx, fmpq


def measure():
    ctx.prec = 192
    pi = arb.pi()
    ratio = fmpq(4749479070945369, 10**23) / fmpq(509892982511772, 10**15)
    height = pi / (80 * arb(ratio**2).log1p())
    values = []
    rows = []
    for numerator in (31, 32, 33):
        w = acb(fmpq(numerator, 64), height)
        zeta = w.zeta()
        factor = 2 * acb(pi)**(-w) * (acb(2)**w - 1)
        residual = factor * zeta
        assert abs(residual) > 0
        values.append(residual)
        rows.append(dict(re_w=f"{numerator}/64", re_s=f"{numerator}/128",
                         zeta=zeta.str(20), residual=residual.str(20)))
    increment = values[-1] - values[0]
    assert abs(increment) > 0
    return dict(height=height.str(45), readings=rows,
                right_residual_minus_left=increment.str(20))


if __name__ == "__main__":
    record = json.dumps(measure(), indent=2) + "\n"
    Path(__file__).with_suffix(".json").write_text(record, encoding="utf-8")
    print(record)
