"""The archived quartic's full Gaussian completion at its real symmetry center."""
import json
import sys
from pathlib import Path

import numpy as np
from flint import arb, ctx


HERE = Path(__file__).resolve().parent
CHUNK = 2**20
N = 32 * CHUNK
END = 18


def denominator_data(repo):
    sys.path.insert(0, str(repo / "tools"))
    from gaussian_moments import signed_counts
    from gaussian_inputs import Q
    bins = []
    partial_sum = 0
    minimum = N
    for start in range(0, N, CHUNK):
        counts = signed_counts(start, start + CHUNK)
        sums = partial_sum + np.cumsum(counts, dtype=np.int64)
        minimum = min(minimum, int(sums.min()))
        partial_sum = int(sums[-1])
        lo = start + 1
        while lo <= min(start + CHUNK, N - 1):
            hi = min(lo + lo // 96, start + CHUNK, N - 1)
            members = sums[lo - start - 1 : hi - start]
            weight = int(members.sum())
            assert int(members.max()) * len(members)**2 < 2**63
            offsets = np.arange(hi-lo+1, dtype=np.int64)
            first_moment = int(np.dot(offsets,members))
            bins.append((lo, hi, weight, first_moment))
            lo = hi + 1
    assert minimum >= 1
    return arb(Q).sqrt() / (2*arb.pi()), bins, minimum, partial_sum


def theta_cells(bscale, bins, last, cells):
    """Enclose exp(x/2) theta(exp(x)/B) on each x-cell in [0,END]."""
    nodes = []
    dx = arb(END) / cells
    for j in range(cells + 1):
        x = j*dx
        u = x.exp() / bscale
        # Discrete Abel summation: theta_N=(1-e^-u)G(u)+S_N exp(-Nu).
        # G is a positive sum through n=N-1. Positive bin totals therefore
        # give pointwise lower/upper bounds using the last/first bin norm.
        lower = sum(((-hi*u).exp()*weight for lo,hi,weight,_ in bins), arb(0))
        upper = sum(((-lo*u).exp()*weight for lo,hi,weight,_ in bins), arb(0))
        finite_last = last*(-N*u).exp()
        factor = -(-u).expm1()
        tail = 2*(-(N+1)*u).exp()*(N+1 + 1/u.expm1())
        nodes.append((lower,upper,finite_last,factor,tail))
    grid = []
    for j in range(cells):
        a,b = nodes[j:j+2]
        x = (j*dx).union((j+1)*dx)
        # G and the final exponential are decreasing in u; 1-exp(-u)
        # is increasing. The unsigned tail is bounded at the lower node.
        low = a[3]*b[0]+b[2]-a[4]
        high = b[3]*a[1]+a[2]+a[4]
        assert low > 0
        kernel = (x/2).exp()*low.union(high)
        grid.append((x,2*dx*kernel))
    return grid


def refine_zero(bscale, bins, last, far):
    """Rigorous positive-weight Gauss rule, with an independent analytic error."""
    width,order=arb(1)/4,14
    h=width/2
    # On every complex unit disk about a panel center, Re(exp(x)/B)>=a.
    # The entire integrand 2 exp(x/2) theta(exp(x)/B) cos(t*x) is
    # bounded by this M uniformly for all |t|<=.27 (t real).
    a=arb(-1).exp()*arb(1).cos()/bscale
    M=4*(arb(END+1)/2).exp()*arb(".27").cosh()/(-(-a).expm1())**2
    error=2*END*M*h**(2*order)/(1-h)
    assert error<arb(".0001")
    rule=[arb.legendre_p_root(order,k,weight=True) for k in range(order)]
    totals=[arb(0),arb(0)]
    heights=[arb(".25835"),arb(".25838")]
    # The first-order expansion in integer norm includes its exact first
    # moment. The positive quadratic error is bounded throughout each bin.
    groups=[(lo,(lo+hi)//2,weight,moment-((hi-lo)//2)*weight,(hi-lo+1)//2)
            for lo,hi,weight,moment in bins]
    for j in range(4*END):
        center=(2*j+1)*h
        for node,gw in rule:
            x=center+h*node
            u=x.exp()/bscale
            v,rem=arb(0),arb(0)
            for lo,m,weight,d,k in groups:
                v+=(-m*u).exp()*(weight-u*d)
                if k:
                    rem+=(-lo*u).exp()*weight*k*k
            gu=v+arb(0).union(rem*u*u/2)
            theta=-(-u).expm1()*gu+last*(-N*u).exp()
            tail=2*(-(N+1)*u).exp()*(N+1+1/u.expm1())
            theta+=arb(0,tail)
            amp=2*h*gw*(x/2).exp()*theta
            for k,t in enumerate(heights):
                totals[k]+=amp*(t*x).cos()
    totals=[v+arb(0,error+far) for v in totals]
    assert totals[0]>0 and totals[1]<0,totals
    return dict(height_bracket=[".25835",".25838"],
                lower_endpoint_value=[str(totals[0].lower()),str(totals[0].upper())],
                upper_endpoint_value=[str(totals[1].lower()),str(totals[1].upper())],
                gauss_error_upper=str(error.upper()))


def certify(bscale, bins, minimum, last):
    # Sum_{n<=Y}|a_n|<=2Y, and u>=1/B. The infinite theta tail
    # |theta-theta_N|/exp(-u) is at most this value, uniformly.
    majorant = 2*(N+1+bscale)*(-N/bscale).exp()
    assert majorant < arb("0.10")
    # x>=18: u=exp(x)/B>40, hence |theta(u)|<=sum 2n exp(-nu)<3 exp(-u).
    # This tail bound covers 2*exp(x/2)*theta(u)*x^2*exp(.02*x), as well
    # as the smaller cosine, sinc and central derivative integrands.
    u_end = arb(END).exp()/bscale
    assert u_end > 40
    tail = 6*arb(END)**2*(arb(".52")*END-u_end).exp()/(u_end-arb(".52")-arb(2)/END)
    assert tail < arb("1e-10")
    grid = theta_cells(bscale,bins,last,1152)
    def value(t):
        return sum((weight*(t*x).cos() for x,weight in grid),arb(0))+arb(0,tail)
    c = value(arb(0))
    curvature = sum((weight*x*x for x,weight in grid),arb(0))+arb(0,tail)
    # If zeta=(s-1/2)^2, Lambda(s)=c+g(zeta), g'(0)=curvature/2.
    # Positivity of the theta kernel bounds |g'(zeta)-g'(0)| on
    # |zeta|<=.02^2 via sinh(.02*x)/(.02*x)-1.
    angle = arb(".02")*END
    distortion = angle.sinh()/angle-1 + tail/curvature
    assert distortion < arb(".023")
    assert arb(".97")*arb(".02")**2 > arb("1.03")*arb(".01")**2
    # Choose the actual common source s=.51, and rho=Lambda(.51)-c.
    # The integral form cosh(y)-1=2 sinh(y/2)^2 prevents cancellation.
    rho = sum((weight*2*(arb(".005")*x).sinh()**2 for x,weight in grid),arb(0))+arb(0,tail)
    # For h(t)=Lambda(1/2+it), -h'(t)/t integrates x^2*sinc(tx).
    low_t,high_t = arb(".25"),arb(".27")
    at_low,at_high = value(low_t),value(high_t)
    assert at_low>0 and at_high<0
    derivative_floors = []
    for j in range(54):
        t = (high_t*j/54).union(high_t*(j+1)/54)
        slope = sum((weight*x*x*(t*x).sinc() for x,weight in grid),arb(0))+arb(0,tail)
        assert slope>0, (j,slope)
        derivative_floors.append(slope.lower())
    def bounds(interval):
        return [str(interval.lower()),str(interval.upper())]
    data = dict(
        completion="Lambda(s)=B^s Gamma(s) L_K(s,eta), with no positive external rescaling",
        coefficient_cutoff=N, minimum_running_signed_sum=minimum, last_running_signed_sum=last,
        theta_tail_relative_to_exp_minus_u_upper=str(majorant.upper()),
        x_domain=[0,END], x_cells=len(grid), x_tail_bound=str(tail.upper()),
        critical_point="1/2", critical_value=bounds(c), second_derivative=bounds(curvature),
        source="0.51",target_radius=bounds(rho), source_disk_radius=".02",
        relative_derivative_distortion_in_squared_coordinate_upper=str(distortion.upper()),
        endpoint_height_bracket=[".25",".27"], value_at_lower_height=bounds(at_low), value_at_upper_height=bounds(at_high),
        lower_bound_minus_height_derivative_over_height=str(min(derivative_floors)),
        counterclockwise_arrival="1/2 + it0",clockwise_arrival="1/2 - it0",
        t0="unique root of Lambda(1/2+it)=0 in (0,.27)")
    data["refinement"]=refine_zero(bscale,bins,last,tail)
    return data


def main():
    if not __debug__:
        raise RuntimeError("Replay requires Python assertions (run without -O)")
    ctx.prec = 96
    repo = HERE.parents[1]
    measured = certify(*denominator_data(repo))
    archived = json.loads((HERE / "central-detours.json").read_text(encoding="utf-8"))
    if measured != archived:
        differences = [key for key in measured.keys() | archived.keys()
                       if measured.get(key) != archived.get(key)]
        raise ValueError(f"Certificate mismatch in {sorted(differences)}")
    print(f"Verified {measured['coefficient_cutoff']:,} norms and all archived intervals.")


if __name__ == "__main__":
    main()
