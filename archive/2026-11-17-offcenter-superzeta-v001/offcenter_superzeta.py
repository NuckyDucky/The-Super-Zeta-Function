"""Freeze a two-dimensional prediction, then count zeros by certified contours.

Requires python-flint and numpy. Run 'python offcenter_superzeta.py predict p.json'
then 'python offcenter_superzeta.py check p.json c.json'. Both outputs are exclusive.
Coordinates are w=beta+i*(H+y), s=w/2, H=x_n(1/4). No direct zeta calls take
place in predict. check counts the normalized reconstructed superzeta by its exact
reference factorization, and separately counts the original cosine determinant.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parent/"deps"))
from flint import acb, acb_poly, arb, ctx


LEVELS = (954985468717,954985468718,954985468719)
OUTER = (Fraction(1,16),Fraction(15,16))
RIGHT = (Fraction(5,8),Fraction(7,8))
HEIGHT_RADIUS = Fraction(1,8)
GRID = 64


def ball(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator


def geometry(n):
    a=n*arb.pi()
    t=arb(1)/4
    h=t/t.tanh()
    # x=a-d, x*tan(d)=h. The root lies between 0 and 2h/a for these n.
    lo,hi=arb(0),(2*h/a).upper()
    def residual(d):
        return (a-d)*d.tan()-h
    assert residual(lo)<0 and residual(hi)>0 and hi<1/a.sqrt()
    for _ in range(110):
        mid=((lo+hi)/2).mid()
        if residual(mid)>0:
            hi=mid
        elif residual(mid)<0:
            lo=mid
        else:
            break
    d=lo.union(hi)
    H=a-d
    eps=H/(d.cos()*t.cosh())
    u=acb(H,t)
    assert (u.cos()**2-(u/eps)**2).contains(0)
    return H,eps


def theta(t):
    return acb(arb(1)/4,t/2).lgamma().imag-t*arb.pi().log()/2


def phasor(t):
    unit=acb(0,t).exp()
    return complex(float(unit.real.mid()),float(unit.imag.mid()))


def phase_polynomial(n):
    H,_=geometry(n)
    scale=(H/(2*arb.pi())).sqrt()
    M=int(scale.floor().unique_fmpz())
    th=theta(H)
    odd=np.arange(1,M+1,2)
    base=np.fromiter((phasor(th-H*arb(int(m)).log()) for m in odd),dtype=complex,count=len(odd))
    phases=np.empty(M,dtype=complex)
    phase2=phasor(-H*arb(2).log())
    power,rot=1,1+0j
    while power<=M:
        count=(M//power+1)//2
        phases[power-1::2*power]=rot*base[:count]
        power,rot=2*power,rot*phase2
    m=np.arange(1,M+1,dtype=float)
    term=phases/np.sqrt(m)
    # Independent variable is z=(y-i*(beta-1/2))/.5. Conjugate coefficients
    # paired in an entire exponential sum give real Taylor coefficients.
    multiplier=.5j*(float(scale.log().mid())-np.log(m))
    coeff=[]
    for j in range(49):
        coeff.append(float(2*term.real.sum()))
        term=term*multiplier/(j+1)
    p=float((scale-M).mid())
    assert abs(math.cos(2*math.pi*p))>.01
    c0=math.cos(2*math.pi*(p*p-p-1/16))/math.cos(2*math.pi*p)
    coeff[0]+=(-1)**(M-1)*c0/math.sqrt(float(scale.mid()))
    return H,M,coeff


def forecast(n):
    H,M,coeff=phase_polynomial(n)
    roots=.5*np.polynomial.polynomial.polyroots(coeff)
    marked=sorted((float(z.real),float(.5-z.imag)) for z in roots
                  if abs(z.real)<float(HEIGHT_RADIUS) and float(OUTER[0])<.5-z.imag<float(OUTER[1]))
    return {"level":n,"height":H.str(35),"modes":M,"degree":48,
            "predicted_roots":[{"height_offset":y,"beta":beta} for y,beta in marked]}


def interpolant(H):
    # Uniform bound on the outer circle comes from Euler--Maclaurin at 1:
    # zeta(w)=1/(w-1)+1/2+w/12 -
    # w(w+1)/2 * integral_1^infinity B_2({x}) x^(-w-2) dx.
    # Re w >= -.4, |B_2|<=1/6, and the disk is pole-free at these heights.
    N=144
    R,r,a=ball("9/10"),ball("3/8"),ball("47/100")
    center=acb(ball("1/2"),H)
    unity=[acb(0,2*arb.pi()*j/N).exp() for j in range(N)]
    values=[(center+r*root).zeta() for root in unity]
    coeff=[sum(v*unity[-j*k%N] for j,v in enumerate(values))/N for k in range(N)]
    bound=(H+3)**2
    error=bound*R/(R-a)*(r**N+a**N)/(R**N-r**N)
    assert error<arb("1e-12")
    noise=arb(0,error)
    polynomial=acb_poly(coeff)
    expansions={}
    def evaluate(beta,y):
        v=acb(beta-ball("1/2"),y)
        assert abs(v)<a
        # Change the polynomial origin to a nearby dyadic node. All
        # coefficients are translated by ball arithmetic; the rounded indices
        # merely choose an origin. This controls interval dependency on edges.
        ix=round(8*float(v.real.mid()))
        iy=round(8*float(v.imag.mid()))
        origin=acb(arb(ix)/8,arb(iy)/8)
        key=(ix,iy)
        if key not in expansions:
            expansions[key]=polynomial(acb_poly([origin/r,1]))
        return expansions[key]((v-origin)/r)+acb(noise,noise)
    return evaluate,error


def winding(evaluate,xrange,yrange=(-HEIGHT_RADIUS,HEIGHT_RADIUS)):
    x0,x1=xrange
    y0,y1=yrange
    corners=((x0,y0),(x1,y0),(x1,y1),(x0,y1),(x0,y0))
    cache={}
    total=arb(0)
    segments=0
    def point(p):
        if p not in cache:
            cache[p]=evaluate(ball(p[0]),ball(p[1]))
        return cache[p]
    def step(a,b,depth):
        nonlocal total,segments
        # A convex half-plane containing the entire image licenses the
        # principal endpoint argument difference, including between samples.
        image=evaluate(ball(a[0]).union(ball(b[0])),ball(a[1]).union(ball(b[1])))
        if not image.contains(0):
            ratio=point(b)/point(a)
            arg=ratio.arg()
            if arg.is_finite() and abs(arg)<arb.pi():
                total+=arg
                segments+=1
                return
        if depth>=23:
            raise ArithmeticError("Unresolved contour segment")
        mid=tuple((v+w)/2 for v,w in zip(a,b))
        step(a,mid,depth+1)
        step(mid,b,depth+1)
    for a,b in zip(corners,corners[1:]):
        step(a,b,0)
    count=(total/(2*arb.pi())).unique_fmpz()
    assert count is not None and count>=0
    return {"count":int(count),"certified_segments":segments}


def candidate_box(root):
    beta=Fraction(str(root["beta"]))
    y=Fraction(str(root["height_offset"]))
    radius=min(Fraction(1,1024),(beta-Fraction(1,2))/4,
               (OUTER[1]-beta)/4,(HEIGHT_RADIUS-abs(y))/4)
    assert radius>0
    return (beta-radius,beta+radius),(y-radius,y+radius)


def verify(record):
    H,eps=geometry(record["level"])
    evaluate,error=interpolant(H)
    def cosine(beta,y):
        u=acb(H+y,ball("1/2")-beta)
        return u.cos()**2-(u/eps)**2
    control=winding(cosine,RIGHT)
    assert control["count"]==1
    control_x,control_y=candidate_box({"beta":.75,"height_offset":0})
    assert winding(cosine,control_x,control_y)["count"]==1
    right=winding(evaluate,RIGHT)
    whole=winding(evaluate,OUTER)
    # Count separate, sign-proven line zeros from the same certified polynomial.
    # The sum over these disjoint intervals is a lower bound with multiplicity.
    def sign(y):
        z=evaluate(ball("1/2"),ball(y))*acb(0,theta(H+ball(y))).exp()
        assert z.imag.contains(0)
        assert z.real>0 or z.real<0
        return 1 if z.real>0 else -1
    ys=[HEIGHT_RADIUS*Fraction(2*j-GRID,GRID) for j in range(GRID+1)]
    signs=[sign(y) for y in ys]
    brackets=[]
    for a,b,left,right_sign in zip(ys,ys[1:],signs,signs[1:]):
        if left==right_sign:
            continue
        for _ in range(19):
            mid=(a+b)/2
            if sign(mid)==left:
                a=mid
            else:
                b=mid
        brackets.append([str(a),str(b)])
    assert len(brackets)<=whole["count"]
    result={"level":record["level"],"cosine_right":control,"superzeta_right":right,
            "superzeta_broad":whole,"line_brackets_offsets":brackets,
            "off_line_upper_bound":whole["count"]-len(brackets),
            "interpolation_uniform_error":error.upper().str(16)}
    for root in record["predicted_roots"]:
        if root["beta"]<=.5:
            continue
        xr,yr=candidate_box(root)
        tested=winding(evaluate,xr,yr)
        result.setdefault("off_axis_forecast_tests",[]).append(
            {"predicted_root":root,"real":list(map(str,xr)),
             "offset":list(map(str,yr)),**tested})
    return result


def save(path,obj):
    with path.open("x",encoding="utf-8",newline="\n") as f:
        f.write(json.dumps(obj,indent=2)+"\n")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["predict","check"])
    parser.add_argument("predictions",type=Path)
    parser.add_argument("certificate",type=Path,nargs="?")
    parser.add_argument("--first",type=int,help="first high cosine level for a new forecast")
    parser.add_argument("--levels",type=int,help="number of consecutive levels to forecast")
    args=parser.parse_args()
    ctx.prec=192
    if args.mode=="predict":
        first=LEVELS[0] if args.first is None else args.first
        count=len(LEVELS) if args.levels is None else args.levels
        if first<=0 or count<=0:
            parser.error("first and levels must be positive")
        result={"positive_height_half_width":"1/8","broad_real":["1/16","15/16"],
                "off_center_real":["5/8","7/8"],"quartet_displacement":"1/4",
                "levels":[forecast(n) for n in range(first,first+count)]}
        save(args.predictions,result)
        print(json.dumps(result,indent=2))
    else:
        if args.certificate is None:
            parser.error("check needs an output certificate path")
        if args.first is not None or args.levels is not None:
            parser.error("check uses the levels in the frozen forecast")
        raw=args.predictions.read_bytes()
        pred=json.loads(raw)
        assert pred["positive_height_half_width"]=="1/8" and pred["quartet_displacement"]=="1/4"
        assert pred["broad_real"]==["1/16","15/16"] and pred["off_center_real"]==["5/8","7/8"]
        levels=[it["level"] for it in pred["levels"]]
        assert levels and levels==sorted(set(levels)) and all(n>0 for n in levels)
        results=[]
        for it in pred["levels"]:
            entry=verify(it)
            results.append(entry)
            print(json.dumps(entry),flush=True)
        save(args.certificate,{"bits":ctx.prec,"prediction_sha256":hashlib.sha256(raw).hexdigest(),
                               "results":results})
