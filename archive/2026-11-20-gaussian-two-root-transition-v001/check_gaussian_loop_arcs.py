"""Actual completed Hecke values on three connected outer contour pieces.

Outputs a common-scale disk enclosure for each node and whole segment.
python-flint 0.9.0. Run from any directory. The other three pieces are
the complex conjugates in reverse order (real, self-dual completion).
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import inf, nextafter
from pathlib import Path
import json

from flint import acb, acb_series, arb, ctx, dirichlet_char

from gaussian_inputs import height
from gaussian_inputs import LIMIT, Q, prime_ideals


def real(q):
    return arb(q.numerator)/q.denominator


def disk(value, log_radius):
    # The exact log differs from log(value) by <= log_radius, locally on
    # a continuous branch. In particular |exp(error)-1| <= exp(radius)-1.
    x, y = float(value.real.mid()), float(value.imag.mid())
    residual = abs(value-acb(x, y)) + abs(value)*log_radius.expm1()
    r = nextafter(float(residual.upper()), inf)
    assert arb(r) >= residual.upper()
    return dict(x=x, y=y, r=r)


def main():
    ctx.prec = 160
    t = height()
    log_b = (arb(Q).sqrt()/(2*arb.pi())).log()
    log_scale = (acb(2,t).lgamma().real + 2*log_b)
    _, ideals = prime_ideals(LIMIT)
    multiplicities = Counter(q for q, _ in ideals)
    counts = Counter(ideals)
    groups = [(arb(q).log(), n, counts[(q,1)], counts[(q,-1)])
              for q,n in multiplicities.items()]

    @lru_cache(None)
    def tail(q):
        # Absolute Euler-log tail majorized by zeta_Q(i)(sigma) with the
        # corresponding initial unramified AND ramified base primes removed.
        # If the Hecke factor omits conductor primes, that only reduces its tail.
        sigma = real(q)
        den = arb(1)
        for ell, n, _, _ in groups:
            local = 1-(-sigma*ell).exp()
            den *= local if n==1 else local*local
        total = acb(sigma).zeta()*acb(sigma).dirichlet_l(dirichlet_char(4,3))
        err = (total.real*den).log()
        assert total.imag.contains(0) and err > 0
        return err.upper()

    # Euler summation: |psi(s)-log(s)| <= (1/2+pi/4)/|Im s| for Re(s)>0.
    # Each absolute log-derivative coefficient is <= twice the rational
    # von Mangoldt coefficient. Bound over all three sides by their common
    # minimum sigma, q-powers already summed in the exact zeta ratio.
    minimum_sigma = arb(9)/8
    zs = acb_series([minimum_sigma,1],prec=2).zeta()
    euler_derivative = -2*(zs[1]/zs[0]).real
    max_t = t+arb(1)/16
    max_abs_s = abs(acb(2,max_t))
    slope_bound = log_b + max_abs_s.log() + arb.pi()/2 + (arb(1)/2+arb.pi()/4)/(t-1) + euler_derivative
    assert slope_bound < 65

    def arc(start, end, n):
        x0,y0 = start
        dx,dy = ((end[0]-x0)/(2*n),(end[1]-y0)/(2*n))
        inc = acb(real(dx),real(dy))
        first = acb(real(x0),t+real(y0))
        # Interleaved midpoint and node evaluations share a geometric step
        # in each Euler prime's q^{-w}. There is no endpoint interpolation.
        prime_terms = [(-first*ell).exp() for ell, *_ in groups]
        steps = [(-inc*ell).exp() for ell, *_ in groups]
        nodes, segments = [], []
        for k in range(2*n+1):
            sigma, dt = x0+k*dx,y0+k*dy
            w = first+k*inc
            den = acb(1)
            for j, (_, _, positive, negative) in enumerate(groups):
                v = prime_terms[j]
                if positive and negative:
                    den *= 1-v*v
                elif positive == 2:
                    den *= (1-v)**2
                elif negative == 2:
                    den *= (1+v)**2
                elif positive:
                    den *= 1-v
                elif negative:
                    den *= 1+v
                prime_terms[j] = v*steps[j]
            value = (w*log_b+w.lgamma()-log_scale).exp()/den
            rad = tail(sigma)
            if k%2:
                segments.append(disk(value,rad+slope_bound*abs(inc)))
            else:
                nodes.append(dict(s=float(sigma),dt=float(dt),**disk(value,rad)))
        return dict(nodes=nodes,segments=segments)

    edges = {name:arc(start,end,n) for name,start,end,n in [
        ("bottom",(F(9,8),F(-1,16)),(F(2),F(-1,16)),112),
        ("right",(F(2),F(-1,16)),(F(2),F(1,16)),96),
        ("top",(F(2),F(1,16)),(F(9,8),F(1,16)),112)]}
    for left,right in (("bottom","right"),("right","top")):
        p=edges[left]["nodes"][-1]
        v=edges[right]["nodes"][0]
        assert abs(complex(p["x"]-v["x"],p["y"]-v["y"])) <= p["r"]+v["r"]
    # The measured path and the polygon through node centers are homotopic
    # away from zero: within each segment both fit in the same convex disk.
    # Hence only the first and last node uncertainties affect the *total*
    # argument. At an internal join identical center coordinates are reused.
    point = lambda row: acb(row["x"],row["y"])
    increment = arb(0)
    for e in edges.values():
        for v,p,q in zip(e["segments"], e["nodes"], e["nodes"][1:]):
            center, radius = point(v), arb(v["r"])
            assert abs(center)>radius
            assert abs(center-point(p))<radius and abs(center-point(q))<radius
            increment += (point(q)/point(p)).arg()
    for first,last in (("bottom","right"),("right","top")):
        assert point(edges[first]["nodes"][-1]) == point(edges[last]["nodes"][0])
    start = edges["bottom"]["nodes"][0]
    end = edges["top"]["nodes"][-1]
    uncertainty = sum((arb(row["r"])/abs(point(row))).asin() for row in (start,end))
    two_arcs = (increment+arb(0,uncertainty.upper()))/arb.pi()
    data=dict(dottie_height=str(t), precision_bits=ctx.prec, prime_norm_cutoff=LIMIT,
              normalized_output="B^w Gamma(w)L(w,eta) / |B^(2+iT_D) Gamma(2+iT_D)|",
              traversal="counterclockwise in input; reflect right arcs by complex conjugation and reverse",
              sigma_observed=[1.125,2], gap_real_parts=[-.125,1.125],
              log_derivative_modulus_global_sup_upper=str(slope_bound.upper()),
              two_outer_arcs_turns=[str(two_arcs.lower()),str(two_arcs.upper())],
              disk_meaning="nodes contain H at one input, segments contain H over the closed input segment",
              edges=edges)
    path=Path(__file__).with_name("gaussian-loop-arcs.json")
    path.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf8")
    for name,edge in edges.items():
        print(name,len(edge["nodes"]),edge["nodes"][0],edge["nodes"][-1])


if __name__ == "__main__":
    main()
