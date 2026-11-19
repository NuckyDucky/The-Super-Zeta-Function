"""Track the zero and the horizontal 1e-6 neighbor by their two distinct Hurwitz levels."""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from flint import acb, arb, acb_series, ctx

HERE=Path(__file__).resolve().parent
if not (HERE/'plane_anchors.py').is_file():
    sys.path.insert(0,str(HERE.parent/'Dottie-Plane-Atlas'))
from plane_anchors import h, hb, hw, square, newton, ball

START=F('13.4091736091859436753')
END=F(15)
GAP=F(1,10**6)

def shift(a): return arb(1)/6+ball(a)/180

def coords(z): return [z.real.mid().str(24,radius=False),z.imag.mid().str(24,radius=False)]

def starts():
    b=shift(START)
    p=newton(acb('-.21015253655603836','37.21583036006284'),b,acb(0),5)
    boxrad=arb('2e-31')
    d=hw(p,b).mid()
    k=abs(1-hw(square(p,boxrad),b)/d)
    assert abs(h(p,b)/d)+k*boxrad<boxrad
    level=h(square(p,boxrad)+ball(GAP),b)
    return (p,p+ball(GAP)),(acb(0),level)

def measurement(angle,nodes,levels,iterations=3):
    b=shift(angle)
    z,q=(newton(node,b,lev,iterations) for node,lev in zip(nodes,levels))
    vel=lambda x:-hb(x,b)/(180*hw(x,b))
    gap=q-z
    logr=((vel(q)-vel(z))/gap).real
    return (z,q), gap, logr

def run(mesh, precision):
    ctx.prec,ctx.cap=precision,3
    nodes,levels=starts()
    original=nodes
    vals=[]
    for i in range(mesh+1):
        a=START+(END-START)*i/mesh
        nodes,g,d=measurement(a,nodes,levels,iterations=5 if i==0 else 4)
        vals.append((a,nodes,g,d))
    events=[]
    for (l,ln,lg,ld),(r,rn,rg,rd) in zip(vals,vals[1:]):
        if float(ld)*float(rd)>=0: continue
        for _ in range(40):
            m=(l+r)/2
            ns,g,d=measurement(m,ln,levels)
            if float(ld)*float(d)<0: r,rn,rd=m,ns,d
            else: l,ln,ld=m,ns,d
        m=(l+r)/2
        ns,g,d=measurement(m,ln,levels)
        events.append(dict(angle=float(m),normalized=float(abs(g)/ball(GAP)),normalized_vector=coords(g/ball(GAP)),neighbor=coords(ns[1]),zero=coords(ns[0])))
    return dict(precision=precision,steps=mesh,initial_levels=[coords(v) for v in levels],start=coords(original[0]),end_zero=coords(vals[-1][1][0]),end_neighbor=coords(vals[-1][1][1]),final_normalized_gap=float(abs(vals[-1][2])/ball(GAP)),final_normalized_vector=coords(vals[-1][2]/ball(GAP)),initial_log_slope=float(vals[0][3]),final_log_slope=float(vals[-1][3]),interior_stationary=events)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE)
    args=parser.parse_args()
    args.output.mkdir(exist_ok=True,parents=True)
    results=[]
    for n,p in [(24,150),(48,210)]:
        result=run(n,p)
        results.append(result)
        print(json.dumps(result),flush=True)
    (args.output/'neighbor.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
