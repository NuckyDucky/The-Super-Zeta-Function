"""Matched test on exactly frozen finite-orbit / pi-grid windows.

Use forecast NOMINATION OUT; then count NOMINATION FORECAST OUT. Heights in
boxes are exact expressions H_arm + rational endpoints. A numerical predictor
per arm is adapted from offcenter_superzeta.phase_polynomial at arbitrary H.
"""
import argparse
import json
import math
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from dottie_grid_nomination import centers, fingerprint, rat, write_new
from offcenter_superzeta import OUTER, RIGHT, acb, arb, ctx, interpolant, phasor, theta, winding
from signed_superzeta_split import candidates, symmetric_horner


HALF = Q(1,4)
ARMS = ("dottie","grid")


def phase_model(H):
    scale = (H/(2*arb.pi())).sqrt()
    M = int(scale.floor().unique_fmpz())
    assert all(((H+rat(y))/(2*arb.pi())).sqrt().floor().unique_fmpz()==M
               for y in (-HALF,HALF))
    th = theta(H)
    odd = np.arange(1,M+1,2)
    base = np.fromiter((phasor(th-H*arb(int(m)).log()) for m in odd),complex,count=len(odd))
    phases = np.empty(M,dtype=complex)
    p2, rot, step = phasor(-H*arb(2).log()),1+0j,1
    while step<=M:
        phases[step-1::2*step]=rot*base[:(M//step+1)//2]
        step,rot=2*step,rot*p2
    m=np.arange(1,M+1,dtype=float)
    term=phases/np.sqrt(m)
    freq=.5j*(float(scale.log().mid())-np.log(m))
    coeff=[]
    for j in range(49):
        coeff.append(float(2*term.real.sum()))
        term=term*freq/(j+1)
    p=float((scale-M).mid())
    assert abs(math.cos(2*math.pi*p))>.01
    coeff[0]+=(-1)**(M-1)*math.cos(2*math.pi*(p*p-p-1/16))/(math.cos(2*math.pi*p)*math.sqrt(float(scale.mid())))
    return M,coeff


def box(x,y):
    return {"beta":list(map(str,x)),"height_offset":list(map(str,y))}


def predict(H):
    M,coeff=phase_model(H)
    roots=sorted((float(z.real),float(.5-z.imag)) for z in .5*np.polynomial.polynomial.polyroots(coeff)
                 if abs(z.real)<float(HALF) and float(OUTER[0])<.5-z.imag<float(OUTER[1]))
    marked=[{"height_offset":y,"beta":b} for y,b in roots]
    positives=[]
    negative=[]
    for h,delta in candidates(marked):
        u,v=symmetric_horner(coeff,h,delta)
        assert max(abs(u),abs(v))<1e-6
        spec={"offset":h,"delta":delta,"even":u,"divided_odd":v}
        if delta>0:
            b=next(Q(str(beta)) for y,beta in roots if y==h and beta>.5)
            yr=Q(str(h))
            pad=min(Q(1,1024),(b-Q(1,2))/4,(OUTER[1]-b)/4,(HALF-abs(yr))/4)
            spec["box"]=box((b-pad,b+pad),(yr-pad,yr+pad))
            positives.append(spec)
        else:
            negative.append(spec)
    control=None
    if negative:
        control=max(negative,key=lambda p:(p["delta"],-p["offset"]))
        ax=[y for y,b in roots if b==.5]
        a,b=next((a,b) for a,b in zip(ax,ax[1:]) if a<control["offset"]<b)
        pad=Q(1,100)
        control["box"]=box(OUTER,(max(-HALF,Q(str(a))-pad),min(HALF,Q(str(b))+pad)))
        control["root_offsets"]=[a,b]
    return {"modes":M,"roots":marked,"positive":positives,"negative_sample":control,
            "broad":box(OUTER,(-HALF,HALF)),"signed_half":box(RIGHT,(-HALF,HALF))}


def certify(H,forecast):
    middle=Q(1,8)
    charts={}
    for center in (-middle,middle):
        charts[center]=interpolant(H+rat(center))
    def count(spec):
        xr=tuple(map(Q,spec["beta"]))
        lo,hi=map(Q,spec["height_offset"])
        pieces=[]
        try:
            for c,(bot,top) in zip((-middle,middle),((-HALF,Q(0)),(Q(0),HALF))):
                a,b=max(bot,lo),min(top,hi)
                if a<b:
                    pieces.append(winding(charts[c][0],xr,(a-c,b-c)))
            return {"status":"certified","count":sum(p["count"] for p in pieces),"pieces":pieces}
        except (ArithmeticError,AssertionError,ValueError) as e:
            return {"status":"unresolved","details":str(e),"completed_pieces":pieces}
    def sign(y):
        c=middle if y>0 else -middle
        val=charts[c][0](rat("1/2"),rat(y-c))*acb(0,theta(H+rat(y))).exp()
        assert val.imag.contains(0)
        return 1 if val.real>0 else (-1 if val.real<0 else 0)
    points=[-HALF+Q(j,256) for j in range(129)]
    signs=[sign(y) for y in points]
    brackets=[]
    for a,b,sa,sb in zip(points,points[1:],signs,signs[1:]):
        if sa*sb!=-1:
            continue
        for _ in range(19):
            mid=(a+b)/2
            sm=sign(mid)
            if sm==sa:
                a=mid
            elif sm==sb:
                b=mid
            else:
                break
        brackets.append((a,b))
    def assign(spec):
        result=count(spec)
        lo,hi=map(Q,spec["height_offset"])
        contained=[p for p in brackets if lo<p[0]<p[1]<hi]
        if result["status"]=="certified":
            assert result["count"]>=len(contained)
            result["off_line_upper_bound"]=result["count"]-len(contained)
            result["line_brackets"]=[list(map(str,p)) for p in contained]
        return result,contained
    broad,_=assign(forecast["broad"])
    control=None
    if forecast["negative_sample"]:
        spec=forecast["negative_sample"]
        control,inside=assign(spec["box"])
        if len(inside)==2 and control.get("off_line_upper_bound")==0:
            a,b=inside
            interval=(-((b[1]-a[0])/2)**2,-((b[0]-a[1])/2)**2)
            control["signed_square_interval"]=list(map(str,interval))
    return {"broad":broad,"signed_half":count(forecast["signed_half"]),
            "positives":[{"forecast":v,"result":count(v["box"])} for v in forecast["positive"]],
            "negative_sample":control,"interpolation_errors":[d[1].upper().str(14) for d in charts.values()]}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["forecast","count"])
    parser.add_argument("nomination",type=Path)
    parser.add_argument("forecast",type=Path)
    parser.add_argument("certificate",type=Path,nargs="?")
    args=parser.parse_args()
    ctx.prec=192
    frozen=json.loads(args.nomination.read_text(encoding="utf-8"))
    d,T,n,G=centers()
    assert frozen["arms"]["grid"]["n"]==n and frozen["source_exact_decimals"]=={
        "x":"4.749479070945369e-8","y":"0.509892982511772","cap":"1"}
    heights=dict(zip(ARMS,(T,G)))
    if args.mode=="forecast":
        pred={"nomination_sha256":fingerprint(args.nomination),"arms":{a:predict(heights[a]) for a in ARMS}}
        write_new(args.forecast,pred)
        print(json.dumps(pred,indent=2),flush=True)
    else:
        assert args.certificate is not None
        pred=json.loads(args.forecast.read_text(encoding="utf-8"))
        assert pred["nomination_sha256"]==fingerprint(args.nomination)
        result={"nomination_sha256":pred["nomination_sha256"],"forecast_sha256":fingerprint(args.forecast),"arms":{}}
        for a in ARMS:
            result["arms"][a]=certify(heights[a],pred["arms"][a])
            print(a,json.dumps(result["arms"][a]),flush=True)
        write_new(args.certificate,result)
