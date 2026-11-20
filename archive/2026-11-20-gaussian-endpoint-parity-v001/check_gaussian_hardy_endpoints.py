"""Directed two-sided enclosures of the quartic's Gaussian Hardy function.

Requires python-flint 0.9.0. Reads the period-640 Dottie height via the
adjacent verification module. Run -B; stdout records all bounds.
"""
import json
from math import isqrt

from flint import acb, arb, ctx
from gaussian_inputs import height
from gaussian_inputs import Q, sign


def coefficients(N):
    # One generator a+bi with a>0, b>=0 for each nonzero Gaussian ideal.
    coeffs = [0] * (N+1)
    for a in range(1, isqrt(N)+1):
        for b in range(isqrt(N-a*a)+1):
            coeffs[a*a+b*b] += sign(a,b)
    assert coeffs[1] == coeffs[2] == 1 and coeffs[73] == 0
    return [(n,c) for n,c in enumerate(coeffs) if c]


def reading(t, B, finite, M):
    s = acb(arb(1)/2,t)
    theta = t*B.log() + s.lgamma().imag
    prefix = 2*sum(c*(theta-t*logn).cos()/root for c,logn,root in finite)

    # W_s(n) is the weight with gamma ratio and tilt exp(z^2-i*pi*z/2).
    # As proved in gaussian-hardy-endpoints.md, |W-1|<=4n/(Bt), and
    # |W|<=2B(t+2)/n. The (uncomputed) middle and outer sums use |a_n|<=d(n).
    assert 10<t and B<2000000 and B*(t+2) < M and M < 2*B*t
    prefix_error = 8*sum(abs(c)*root for c,logn,root in finite)/(B*t)
    sqr = arb(M).sqrt()
    logM = arb(M).log()
    middle_error = 36*sqr*(1+logM)
    outer_error = 12*B*(t+2)*(logM+3)/sqr
    err = prefix_error+middle_error+outer_error
    low, high = (prefix-err).lower(), (prefix+err).upper()
    assert low<0<high
    return {"height":str(t), "finite_Hardy_polynomial":str(prefix),
            "finite_weight_approximation_error_lt":str(prefix_error.upper()),
            "uncalculated_middle_error_lt":str(middle_error.upper()),
            "uncalculated_outer_error_lt":str(outer_error.upper()),
            "resolution":"indeterminate", "Hardy_lower":str(low), "Hardy_upper":str(high)}


def cutoff_sweep(coeffs, B, ts):
    """Compare the finite polynomials; their signs alone do not certify a zero."""
    phase=[t*B.log()+acb(arb(1)/2,t).lgamma().imag for t in ts]
    values=[arb(0) for t in ts]
    ix=0
    records=[]
    for power in range(10,21,2):
        N=2**power
        while ix < len(coeffs) and coeffs[ix][0] <= N:
            n,c=coeffs[ix]
            logn=arb(n).log()
            amp=2*c/arb(n).sqrt()
            for j,t in enumerate(ts):
                values[j] += amp*(phase[j]-t*logn).cos()
            ix+=1
        records.append(dict(cutoff=N, left=str(values[0]), right=str(values[1])))
    return records


def main():
    ctx.prec = 160
    N=65536
    M=8*10**18
    coeffs=coefficients(2**20)
    B=arb(Q).sqrt()/(2*arb.pi())
    finite=[(c,arb(n).log(),arb(n).sqrt()) for n,c in coeffs if n<=N]
    center=height()
    rec={"precision_bits":ctx.prec, "factor":"untwisted eta_delta",
         "normalization":"Re(exp(i*(t log B + Im logGamma(1/2+it)))*L(1/2+it,eta))",
         "norm_cutoff":N, "nonzero_norm_coefficients":len(finite), "tail_split":M,
         "conductor_Q":Q, "balanced_length_Bt":str(B*center),
         "endpoints":{o:reading(center+arb(k)/16,B,finite,M) for o,k in [("-1/16",-1),("+1/16",1)]},
         "finite_cutoff_sweep":cutoff_sweep(coeffs,B,[center-arb(1)/16,center+arb(1)/16])}
    print(json.dumps(rec,indent=2))


if __name__ == "__main__":
    main()
