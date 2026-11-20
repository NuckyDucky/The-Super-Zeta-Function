"""Gaussian endpoint bounds. With the archived gaussian_inputs module on PYTHONPATH,
run python -B check_endpoint_refinement.py. Requires python-flint 0.9.0.
"""
import json
from math import isqrt

from flint import acb, arb, ctx
from gaussian_inputs import Q, height, sign, prime_ideals


def norm_coefficients(limit):
    coefficients = [0] * (limit + 1)
    for a in range(1, isqrt(limit) + 1):
        for b in range(isqrt(limit - a*a) + 1):
            coefficients[a*a + b*b] += sign(a, b)
    assert coefficients[1] == coefficients[2] == 1 and coefficients[73] == 0
    return coefficients


def finite_polynomials(coefficients, B, endpoints, limit):
    phases = [t * B.log() + acb(arb(1)/2, t).lgamma().imag for t in endpoints]
    values = [arb(0), arb(0)]
    mass = arb(0)
    sweep = []
    # A measured lower bound on the price of discarding the oscillatory signs
    # of just the next equally long block in the real V-weighted sum.
    next_block_abs = [arb(0), arb(0)]
    for n, coefficient in enumerate(coefficients):
        if coefficient:
            log_n = arb(n).log()
            amplitude = 2*coefficient/arb(n).sqrt()
            if n <= limit:
                mass += abs(amplitude)
            for j, t in enumerate(endpoints):
                term = amplitude * (phases[j] - t * log_n).cos()
                if n <= limit:
                    values[j] += term
                else:
                    next_block_abs[j] += abs(term)
        if n in (2**16, 2**18, 2**20, 2**21):
            sweep.append({"norm_cutoff": n, "lower_endpoint": str(values[0]),
                          "upper_endpoint": str(values[1])})
    lower_v = ((2*limit/(B*endpoints[0])).log()/2).erfc()/2
    return sweep, values, mass, [(lower_v*v).lower() for v in next_block_abs]


def upper_tail(U, limit, density, error):
    return (4 * density * U.sqrt() * (arb(1)/4).exp()
            + 2 * error * (1 + ((U/limit).log() + 2/arb.pi().sqrt())/2))


def sieve_constants(U, limit):
    _, ideals = prime_ideals(100000)
    grouped = {}
    for norm, symbol in ideals:
        grouped.setdefault(norm, []).append(symbol)
    candidates = sorted(p for p, signs in grouped.items() if sorted(signs) == [-1, 1])
    assert 73 in candidates
    density, error = arb.pi()/4, arb(1)
    best = upper_tail(U, limit, density, error)
    best_values = (0, 0, density, error)
    for count, p in enumerate(candidates, 1):
        root = arb(p).sqrt()
        density *= arb(p-1)/(p+1)
        error *= (root+1)/(root-1)
        bound = upper_tail(U, limit, density, error)
        if bound < best:
            best = bound
            best_values = (count, p, density, error)
    return best_values


def endpoint(t, center, B, limit, density, error, polynomial, mass):
    pi = arb.pi()
    U = B*t
    assert t > 10**12 and U > limit
    near = ((arb(1).exp()/(2*pi)) * ((2+pi/4)*pi.sqrt()+1)
            * (arb(210)/(t-14)).exp()/(t-14))
    far = (arb(-143).exp()/(2*pi)
           * ((1+arb(2).sqrt()*(1+1/(2*t)))/12 + arb(2).sqrt()/t))
    assert t*(near+far) < 3
    # For all n use |W_s(n)-V_U(n)| <= 3B/n. beta(3/2) <= 1 by alternation.
    weight_error = 6*B*(arb(3)/2).zeta()
    loggap = (U/limit).log()/2
    prefix_error = mass * (-loggap**2).exp()/(2*pi.sqrt()*loggap)
    omitted = upper_tail(U, limit, density, error)
    radius = weight_error + prefix_error + omitted
    low, high = (polynomial-radius).lower(), (polynomial+radius).upper()
    assert low < 0 < high
    # Common positive normalization S=B^2 |Gamma(2+iT_D)|.
    log_scale = (-arb(3)/2*B.log() + acb(arb(1)/2, t).lgamma().real
                 - acb(2, center).lgamma().real)
    scale = log_scale.exp()
    return {"height": str(t), "raw_polynomial": str(polynomial),
            "gamma_weight_error_lt": str(weight_error.upper()),
            "finite_smoothing_error_lt": str(prefix_error.upper()),
            "omitted_smoothed_radius_lt": str(omitted.upper()),
            "hardy_lower": str(low), "hardy_upper": str(high),
            "completed_normalized_lower": str((scale*low).lower()),
            "completed_normalized_upper": str((scale*high).upper()),
            "sign": "unresolved"}


def main():
    ctx.prec = 192
    limit = 2**21
    T = height()
    endpoints = [T-arb(1)/16, T+arb(1)/16]
    B = arb(Q).sqrt()/(2*arb.pi())
    coefficients = norm_coefficients(2*limit)
    sweep, polynomials, mass, block_min = finite_polynomials(coefficients, B, endpoints, limit)
    count, cutoff_prime, density, error = sieve_constants(B*endpoints[1], limit)
    result = {"precision_bits": ctx.prec, "norm_cutoff": limit, "Q": Q,
              "opposite_split_primes": count, "largest_prime_used": cutoff_prime,
              "absolute_count_linear_coefficient": str(density),
              "absolute_count_sqrt_coefficient": str(error), "polynomial_sweep": sweep,
              "absolute_cosine_contribution_norms_(N,2N]_lower": [str(v) for v in block_min],
              "endpoints": [endpoint(t, T, B, limit, density, error, p, mass)
                            for t, p in zip(endpoints, polynomials)]}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
