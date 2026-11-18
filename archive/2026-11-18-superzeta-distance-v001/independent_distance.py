"""Verify the public distance constants using a single chart per whole window.

Read the proposed coverage and distance files. Independently check every root
bracket, a winding around the whole rectangle, and all nine proposed bounds.
"""
import argparse
import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

from flint import acb, acb_poly, arb, ctx


def ball(value):
    value = Fraction(value)
    return arb(value.numerator)/value.denominator


def whole_chart(H, cached_samples=None):
    count = 145
    R, r, a = map(ball, ("59/40","18/25","71/100"))
    assert (ball("1/2")**2*2).sqrt() < a < r < R
    # At every point of the R-disk, Re w >= -39/40. Euler summation
    # through periodic B2 bounds the tail by (H+4)^2/[12*(1/40)].
    bound = 5*(H+4)**2
    assert 2+(H+4)/12+(H+4)**2/(12*ball("1/40")) < bound
    error = bound/(1-a/R)*((a/R)**count+(r/R)**count)/(1-(r/R)**count)
    assert error < ball("1e-14")
    origin = acb(ball("1/2"),H)
    units = [acb(0,2*arb.pi()*j/count).exp() for j in range(count)]
    if cached_samples:
        samples=[acb(arb(v[0]),arb(v[1])) for v in json.loads(cached_samples.read_bytes())]
        assert len(samples)==count
    else:
        samples = []
        for unit in units:
            w=origin+r*unit
            if w.real>ball("1/12"):
                value=w.zeta()
            else:
                chi=((w-ball("1/2"))*arb.pi().log()+((1-w)/2).lgamma()-(w/2).lgamma()).exp()
                value=chi*(1-w).zeta()
            samples.append(value)
    assert all(z.is_finite() and z.real.rad()<ball("1e-12") and z.imag.rad()<ball("1e-12") for z in samples)
    poly=acb_poly([sum(samples[j]*units[(-j*k)%count] for j in range(count))/count
                  for k in range(count)])

    @lru_cache(maxsize=None)
    def shifted(ix,iy):
        center=acb(arb(ix)/32,arb(iy)/32)
        return center,poly(acb_poly([center/r,1]))

    def evaluate(x,y):
        w=acb(x,y)
        assert abs(w)<a
        center,local=shifted(round(32*float(x.mid())),round(32*float(y.mid())))
        return local((w-center)/r)+acb(arb(0,error),arb(0,error))
    return evaluate


def verify(coverage_path, distance_path, cached_samples=None):
    coverage = json.loads(coverage_path.read_bytes())
    distances = json.loads(distance_path.read_bytes())
    ctx.prec=192
    q = Fraction
    k=coverage["harmonic"]
    assert k in (2,3) and k==distances["harmonic"]
    x,y=map(ball,("4.749479070945369e-8","0.509892982511772"))
    H=2*k*arb.pi()/(160*((x/y)**2).log1p())
    evaluate=whole_chart(H,cached_samples)
    brackets=[tuple(map(q,p["offset"])) for piece in coverage["cells"] for p in piece["brackets"]]
    assert all(-q(1,2)<l<h<q(1,2) for l,h in brackets)
    assert all(p[1]<n[0] for p,n in zip(brackets,brackets[1:]))

    def hardy(y):
        t=H+ball(y)
        theta=acb(ball("1/4"),t/2).lgamma().imag-t*arb.pi().log()/2
        value=acb(0,theta).exp()*evaluate(arb(0),ball(y))
        assert value.imag.contains(0)
        return value.real

    assert all(hardy(l)*hardy(h)<0 for l,h in brackets)

    def segments(lo,hi,n):
        vertices=[(-q(1,2),lo),(q(1,2),lo),(q(1,2),hi),(-q(1,2),hi),(-q(1,2),lo)]
        for (a,b),(c,d) in zip(vertices,vertices[1:]):
            for j in range(n):
                x0,x1=[ball(a+(c-a)*v/n) for v in (j,j+1)]
                y0,y1=[ball(b+(d-b)*v/n) for v in (j,j+1)]
                yield (x0,y0),(x1,y1),x0.union(x1),y0.union(y1)

    argument=arb(0)
    for start,end,X,Y in segments(-q(1,2),q(1,2),400):
        z=evaluate(X,Y)
        assert not z.contains(0)
        turn=(evaluate(*end)/evaluate(*start)).arg()
        assert abs(turn)<arb.pi()
        argument+=turn
    actual=(argument/(2*arb.pi())).unique_fmpz()
    assert actual==len(brackets)==coverage["full_count"]==len(distances["cells"])

    cuts=[-q(1,2),*((p[1]+n[0])/2 for p,n in zip(brackets,brackets[1:])),q(1,2)]
    common=None
    lower_checks=[]
    for i,(l,h) in enumerate(brackets):
        proposed=distances["cells"][i]
        assert tuple(map(q,proposed["height_offset_cell"]))==(cuts[i],cuts[i+1])
        assert tuple(map(q,proposed["root_height_offset_bracket"]))==(l,h)
        root=ball(l).union(ball(h))
        minimum=arb(10**12)
        for _,_,X,Y in segments(cuts[i],cuts[i+1],400):
            beta=X+ball("1/2")
            phase=(acb(beta,H+Y)*arb(2).log()).exp()-1
            ratio=2*(-beta*arb.pi().log()).exp()*abs(phase)*abs(evaluate(X,Y))/abs(acb(X,Y-root))
            minimum=arb.min(minimum,ratio.lower())
        c=q(proposed["factor_lower_bound_w_units"])
        assert minimum>=ball(c)>0,(i,minimum,c)
        lower_checks.append(int((minimum*1000).floor().unique_fmpz()))
        common=c if common is None else min(common,c)
    assert common==q(distances["distance_coefficient_w"])
    assert 2*common==q(distances["distance_coefficient_s"])
    print(f"H{k}, winding {actual}, independently certified lower bounds in 1/1000 w-units: {lower_checks}; every published constant passed.")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coverage",type=Path)
    parser.add_argument("distance",type=Path)
    opts=parser.parse_args()
    verify(opts.coverage,opts.distance)
