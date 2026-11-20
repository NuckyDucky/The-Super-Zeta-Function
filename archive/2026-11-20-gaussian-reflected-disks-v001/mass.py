"""Positive compact-support explicit-formula test for the reflected Dottie disks."""
import json
import sys
from pathlib import Path

from flint import arb, ctx

from gaussian_inputs import Q, height, prime_ideals


def enclosure(x):
    return {"lower": x.lower().str(26), "upper": x.upper().str(26)}


def run(cutoff):
    ctx.prec = 192
    pi = arb.pi()
    t = height() - arb(2)/1024
    radius = arb(15)/1024
    band = arb(cutoff).log()
    def window(v):
        return (1-v/band)*(pi*v/band).cos()+(pi*v/band).sin()/pi
    def multiplier(v):
        return window(v)/(v/2).cosh()

    # h(u) >= 0, integral h(u) du/(2pi)=1, variance = -multiplier''(0).
    var = (pi/band)**2 + arb(1)/4
    # First Bernoulli remainder in Re psi(1/2+iv) is <=min(1,pi/(4|v|)).
    # Use the latter when |u|<=T/2 and Chebyshev outside.
    arch = arb(Q).sqrt()/(2*pi)
    arch_upper = 2*(arch.log() + (1+t+var.sqrt()).log()
                    + pi/(2*t) + 4*var/t**2)

    _, ideals = prime_ideals(cutoff)
    weights = {}
    for q, chi in ideals:
        if chi == 0:
            continue
        n = q
        sign = chi
        logq = arb(q).log()
        while n <= cutoff:
            weights[n] = weights.get(n, arb(0)) + sign*logq
            sign *= chi
            n *= q
    prime_sum = arb(0)
    for n, coeff in weights.items():
        if coeff == 0 or n == cutoff:
            continue
        ln = arb(n).log()
        prime_sum += 2*coeff*multiplier(ln)*(ln*t).cos()/arb(n).sqrt()

    total_upper = (arch_upper-prime_sum).upper()
    # Right-endpoint rectangles: window, sech and cos(radius*v) decrease.
    bins = 4096
    assert band*radius < pi/2
    lower = arb(0)
    for j in range(1,bins):
        v = band*j/bins
        lower += multiplier(v)*(radius*v).cos()
    per_zero = (2*band/bins*lower).lower()
    assert per_zero > 0
    ratio = total_upper/(2*per_zero)
    return dict(precision_bits=ctx.prec,bandlimit="log("+str(cutoff)+")",cutoff=cutoff,
                height_offset="-2/1024",center_real="528/1024",radius="15/1024",
                arch_upper=arch_upper.upper().str(28),prime_sum=enclosure(prime_sum),
                total_upper=total_upper.str(28),single_zero_min=per_zero.str(28),
                ratio_upper=ratio.upper().str(28),upper_count=int(ratio.upper().floor().unique_fmpz()))


if __name__ == "__main__":
    result = run(int(sys.argv[1]) if len(sys.argv)>1 else 100000)
    payload = json.dumps(result, indent=2) + "\n"
    if len(sys.argv)>2:
        Path(sys.argv[2]).write_text(payload,encoding="utf-8")
    print(payload, end="")
