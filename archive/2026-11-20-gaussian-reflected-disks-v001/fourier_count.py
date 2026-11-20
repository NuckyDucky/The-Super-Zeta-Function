"""Positive explicit-formula count for the two proposed Gaussian disks.

Fourier convention: h(z) = (1/pi) integral_0^A g(u) cos(zu) du.
g is the normalized autocorrelation of cos(pi v/A) on [-A/2,A/2],
divided by cosh(u/2). On the edges Im z=+-1/2, Re h is the inverse
Fourier transform of that autocorrelation, hence nonnegative. Two
integrations by parts give O((1+|Re z|)^-2) on the closed strip, so
the harmonic minimum principle gives positivity everywhere between.
The zero sum converges absolutely. The shifted test is admissible in
the classical Weil explicit formula (or smooth its Fourier transform
by convolution and apply dominated convergence).

Each zero in the closed band |gamma-t|<=r contributes at least the
right Riemann sum below: cos(du)>=cos(ru)>=0, cosh((beta-1/2)u)>=1.
The two disjoint disks contribute equal counts by self-duality.

Gamma integral: h >= 0 on the real line and integral h = g(0) = 1.
Write g=p*q for q=sech(u/2). On [0,A], 0<=p<=1, |p'|<=pi/A,
|p''|<=(pi+pi^2)/A^2, |q'|<=1/2, |q''|<=q/4 and integral q<=pi.
Also integral |q'|<=1. At A and 0, g'=0. Thus
  pi x^2 |h(x)| <= integral |g''| <= (3*pi+pi^2)/A + pi/4.
We use the loose bound |h(x)| <= 10/x^2 for A>=4.
The first-order Euler summation bound on digamma gives
Re psi(1/2+iv) <= log(1+|v|)+2 globally and, for positive v,
<= log(1+v)+(1/2+pi/4)/v. Split at |x|=M and bound the outer
integral using 10/x^2, integrating log(1+t+x) by parts.
For the conductor Q, completion (sqrt(Q)/(2*pi))^s Gamma(s), and
real primitive Hecke character, the arithmetic formula is
  sum Re h((rho-1/2)/i-t)
    = [log B + integral h(x) Re psi(1/2+i(t+x)) dx
       - sum 2 Lambda_eta(n) p(log n) cos(t log n)/(n+1)]/pi.
Here p has argument u, not u/A. The prime-power sum is exactly finite.
"""
import argparse
import json
from collections import Counter
from pathlib import Path

from flint import arb, ctx

from gaussian_inputs import Q, height, prime_ideals


def check(cutoff):
    ctx.prec = 160
    pi = arb.pi()
    t = height() - arb(1)/512
    r = arb(15)/1024
    A = arb(cutoff).log()
    assert A >= 4 and A*r < pi/2

    def taper(u):
        v = u/A
        return (1-v)*(pi*v).cos() + (pi*v).sin()/pi

    _, ideals = prime_ideals(cutoff)
    arithmetic = arb(0)
    for (q, sign), frequency in Counter(ideals).items():
        if not sign:
            continue
        logq = arb(q).log()
        n, k = q, 1
        while n <= cutoff:
            u = k*logq
            arithmetic += 2*frequency*sign**k*logq*taper(u)*(t*u).cos()/(n+1)
            n *= q
            k += 1
    M = 10**6
    gamma_upper = ((t+M+1).log() + (arb(1)/2+pi/4)/(t-M)
                   + 20*(((t+M+1).log()+2)/M + ((t+1)/M).log1p()/(t+1)))
    total_upper = (arb(Q).sqrt().log() - (2*pi).log()+gamma_upper-arithmetic)/pi
    cells = 8192
    du = A/cells
    floor_weight = sum(taper(k*du)*(k*du*r).cos()/(k*du/2).cosh()
                       for k in range(1,cells+1))*du/pi
    assert floor_weight > 0
    ratio = total_upper.upper()/floor_weight.lower()
    band = int(ratio.upper().floor().unique_fmpz())
    return dict(precision_bits=ctx.prec, cutoff=cutoff, height=str(t),
                disk_radius="15/1024", right="33/64", left="31/64",
                gamma_integral_upper=str(gamma_upper.upper()),
                signed_prime_term_before_dividing_by_pi=str(arithmetic),
                trace_upper=str(total_upper.upper()), per_zero_lower=str(floor_weight.lower()),
                ratio_upper=str(ratio.upper()), closed_band_count_at_most=band,
                count_per_closed_disk_at_most=band//2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", type=int, default=2**20)
    parser.add_argument("--save", type=Path)
    args = parser.parse_args()
    record = json.dumps(check(args.cutoff),indent=2)
    if args.save:
        args.save.write_text(record+"\n", encoding="utf-8")
    print(record)
