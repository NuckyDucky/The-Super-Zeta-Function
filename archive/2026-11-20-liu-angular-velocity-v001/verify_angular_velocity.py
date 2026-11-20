"""Replay the angular-speed bounds using Python 3.12 and python-flint 0.9.0."""

import argparse
import json
from pathlib import Path

import flint
from flint import acb, acb_series, arb, ctx, dirichlet_char, fmpq, fmpq_poly


def isolate_endpoint():
    """Count the roots of Liu's polynomial in each open interval over the rationals."""
    x = fmpq_poly([0, 1])
    p = 7*(7-6*x)**4*(9*x-7)**5 - 3888*19**5*(15*x-13)**4*(1-x)**5
    sequence = [p, p.derivative()]
    while sequence[-1].degree() > 0:
        remainder = -(sequence[-2] % sequence[-1])
        assert remainder != 0
        sequence.append(remainder)

    def variations(t):
        values = [polynomial(t) for polynomial in sequence]
        signs = [v > 0 for v in values if v != 0]
        return sum(a != b for a, b in zip(signs, signs[1:]))

    narrow = (fmpq(87334585610671857, 10**17), fmpq(87334585610671858, 10**17))
    broad = (fmpq(13, 15), fmpq(7, 8))
    assert broad[0] < narrow[0] < narrow[1] < broad[1]
    assert 1 - narrow[1] > fmpq(12665414389, 10**11)
    intervals = []
    for left, right in (broad, narrow):
        assert p(left) != 0 and p(right) != 0
        counts = (variations(left), variations(right))
        assert counts[0] - counts[1] == 1
        intervals.append({"open_interval": [str(left), str(right)], "sturm_variations": counts})
    return intervals


def speed_bounds(beta_floor):
    """Euler-product estimates at a lower bound on the real part of a zero."""
    s = 1 + beta_floor
    q = arb(3)**(-beta_floor)
    p = arb(3)**(-s)
    lower = 3/arb.pi() * (1+p)*(2*s).zeta() / ((1+q)*s.zeta())
    upper = 3/arb.pi() * (1-p)*s.zeta() / (1-q)
    return lower, upper


def hurwitz_velocity(rho, shift):
    """Compute -R_a/R_w directly from the two Hurwitz summands."""
    other = 1 - shift
    w = acb_series([rho, 1], prec=2)
    pair = w.zeta(shift) + w.zeta(other)
    # After removing pi^(-w), differentiating in w still contributes -log(pi)*pair.
    dw = pair[1] - arb.pi().log()*pair[0]
    da = rho/arb.pi() * ((rho+1).zeta(shift) - (rho+1).zeta(other))
    assert pair[0].contains(0) and not dw.contains(0)
    return -da/dw


def enclosed_zero(value):
    assert value.contains(0) and abs(value) < arb("1e-65")
    return str(abs(value).upper())


def measure_zero(index, character):
    rho = acb.zeta_zero(index)
    zeta_series = acb_series([rho, 1], prec=2).zeta()
    assert zeta_series[0].contains(0) and not zeta_series[1].contains(0)
    plus = hurwitz_velocity(rho, arb(1)/3)
    minus = hurwitz_velocity(rho, arb(2)/3)
    arithmetic = (1+rho).dirichlet_l(character) / (1-acb(3)**(-rho))
    predicted = -3*rho*arithmetic / (arb.pi()*zeta_series[1])
    speed = abs(plus*zeta_series[1]/rho)
    assert arb("0.33217") < speed < arb("4.76646")
    return {"index": index, "riemann_zero": str(rho),
            "velocity_at_positive_angle": str(plus), "velocity_at_negative_angle": str(minus),
            "normalized_speed": str(speed), "opposite_velocity_residual": enclosed_zero(plus+minus),
            "arithmetic_velocity_residual": enclosed_zero(plus-predicted)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.prec = 256
    ctx.cap = 2
    cases = [
        ("seven_eighths", arb(1)/8, "0.11197", "45.333"),
        ("liu_endpoint", arb(12665414389)/10**11, "0.11325", "44.270"),
        ("critical_line", arb(1)/2, "0.33217", "4.76646"),
    ]
    bounds = {}
    for name, beta_floor, rounded_lower, rounded_upper in cases:
        lower, upper = speed_bounds(beta_floor)
        assert arb(rounded_lower) < lower < upper < arb(rounded_upper)
        bounds[name] = {"beta_floor": str(beta_floor), "lower_estimate": str(lower),
                        "upper_estimate": str(upper), "outward_rounding": [rounded_lower, rounded_upper]}
    chi = dirichlet_char(3, 2)
    assert chi(1) == 1 and chi(2) == -1 and chi(3) == 0
    report = {"python_flint": flint.__version__, "precision_bits": ctx.prec,
              "isolating_intervals": isolate_endpoint(), "speed_bounds": bounds,
              "first_ten_zeros": [measure_zero(k, chi) for k in range(1, 11)]}
    data = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8", newline="\n")
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
