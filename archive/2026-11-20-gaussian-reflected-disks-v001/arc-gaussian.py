"""Directed two-piece Gaussian smoothed functional equation on an entire circle.

Run with python-flint 0.9.0. See arc-method.md for the tail estimates.
"""
import argparse
import json
from math import isqrt
from pathlib import Path
from math import factorial

from flint import arb, acb, ctx
from gaussian_inputs import Q, height, sign


def norm_coeffs(N):
    coeffs = [0] * (N + 1)
    for a in range(1, isqrt(N) + 1):
        for b in range(isqrt(N - a*a) + 1):
            coeffs[a*a + b*b] += sign(a, b)
    assert coeffs[1] == coeffs[2] == 1 and coeffs[73] == 0
    return [(arb(n).log(), c) for n, c in enumerate(coeffs) if c]


def integral_bound(a):
    tlo, thi = T-arb(1)/32, T+arb(1)/32
    d0 = min(abs(a-arb(46)/100), abs(a-arb(54)/100))
    d1 = max(abs(a-arb(46)/100), abs(a-arb(54)/100))
    assert d0 > 0 and (a < arb(46)/100 or a > arb(54)/100)
    if a < arb(1)/2:
        near = (tlo-20)**(a-arb(1)/2)
        b = arb(1)/2
    else:
        near = (thi+22)**(a-arb(1)/2)
        b = arb(3)/2
    near *= (2*abs(a-arb(1)/2)/(tlo-20)).exp()
    assert a.gamma()/b.gamma() < 16
    far = 16*arb(-400).exp()*((thi+1)/20+1)
    common = (B**(a-2)*(arb.pi()/64).exp()/
              (2*arb.pi()*(T*(1+T*T)).sqrt()))
    return common * (d1*d1).exp()/d0 * (arb.pi().sqrt()*near + far)


def gamma(delta):
    e = 3*abs(delta)/(T-1)
    return gamma0*(delta*logBt + acb(arb(0,e.upper()),arb(0,e.upper()))).exp()


def prefix(delta):
    p=acb(0)
    for c in reversed(coeff_taylor):
        p=p*delta+c
    x=abs(delta)*arb(N).log()
    err=(mass*x.exp()*x**(order+1)/factorial(order+1)).upper()
    return gamma(delta)*(p+acb(arb(0,err),arb(0,err)))


def partial(x,y):
    return prefix(acb(x-arb(1)/2,y)) + prefix(acb(arb(1)/2-x,y)).conjugate()


def pos(angle):
    return (arb(33)/64+arb(15)/1024*angle.cos(),
            -arb(1)/512+arb(15)/1024*angle.sin())


if __name__ == '__main__':
    ctx.prec = 192
    parser = argparse.ArgumentParser()
    parser.add_argument('--cutoff',type=int,default=16384)
    parser.add_argument('--arcs',type=int,default=64)
    parser.add_argument('--save', type=Path, help='write the full arc enclosures to this path')
    args=parser.parse_args()
    N, K = args.cutoff, args.arcs
    assert N>=73 and K>=4 and K%4==0
    T = height()
    B = arb(Q).sqrt()/(2*arb.pi())
    logBt = acb((B*T).log(),arb.pi()/2)
    s0 = acb(arb(1)/2,T)
    gamma0 = (((s0-2)*B.log()) + s0.lgamma()-acb(2,T).lgamma().real).exp()
    coeffs = norm_coeffs(N)
    terms = [(ln,c*(-s0*ln).exp()) for ln,c in coeffs]
    order=16
    mass=sum(abs(term) for _,term in terms)
    coeff_taylor = [acb(0) for _ in range(order+1)]
    for ln,term in terms:
        c=term
        for k in range(order+1):
            coeff_taylor[k]+=c
            c*=(-ln)/(k+1)
    a, b = arb(1)/16, arb(1)+arb(1)/32
    short = sum(abs(c)*(-a*ln).exp() for ln,c in coeffs)
    tail = b.zeta() - sum(abs(c)*(-b*ln).exp() for ln,c in coeffs)
    assert tail > 0
    finite_err = 2*integral_bound(a)*short
    upper_err = 2*integral_bound(b)*tail
    error = finite_err + upper_err
    disk = acb(arb(0,error.upper()),arb(0,error.upper()))
    rows = []
    radius = arb.pi()/K
    maxsize = arb(0)
    maxreal = -arb(1)
    minreal = arb(1)
    minmod = arb(1)
    angles=[]
    for j in range(K):
        mid = (2*j+1)*radius
        arc = mid + arb(0,radius.upper())
        x,y=pos(arc)
        val=partial(x,y)
        maxsize=max(maxsize,abs(val).upper())
        maxreal=max(maxreal,val.real.upper())
        minreal=min(minreal,val.real.lower())
        minmod=min(minmod,abs(val).lower())
        angles.append(partial(*pos(2*j*radius)))
        total=val+disk
        rows.append({'arc':j,'prefix':str(val),'value':str(total),
                     'contains_zero':total.contains(0)})
    points=angles[::K//4]
    # A convex arc rectangle avoiding 0 is in an open half-plane through 0.
    # The principal endpoint argument differences then add the actual winding.
    finite_winding=None
    if minmod>0:
        winding=sum((angles[(j+1)%K]/angles[j]).arg() for j in range(K))/(2*arb.pi())
        integer=winding.unique_fmpz()
        assert integer is not None
        if minmod>finite_err:
            finite_winding=int(integer)
    result = {'precision_bits':ctx.prec,'N':N,'nonzero_coefficients':len(coeffs),
              'disk_center':'33/64+i(T_D-1/512)','disk_radius':'15/1024',
              'full_circle_ccw_arcs':K,'scale':'B^2 |Gamma(2+iT_D)|',
              'short_weight_error_bound':str(finite_err.upper()),
              'omitted_norm_error_bound':str(upper_err.upper()),
              'largest_arc_prefix_modulus_bound':str(maxsize),
              'maximum_arc_prefix_real_part_upper':str(maxreal),
              'minimum_arc_prefix_real_part_lower':str(minreal),
              'minimum_arc_prefix_modulus_lower':str(minmod),
              'exact_smoothed_finite_winding':finite_winding,
              'maximum_smoothed_prefix_real_part_upper':str((maxreal+finite_err).upper()),
              'prefix_at_east_north_west_south':[str(p) for p in points],
              'arcs_containing_zero':sum(r['contains_zero'] for r in rows),'arcs':rows}
    if args.save:
        args.save.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='arcs'},indent=2))
