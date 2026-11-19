"""Certify both continued levels and the single maximum of their finite separation."""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
from flint import arb, acb_series, ctx
from neighbor import START, END, GAP, HERE, starts, shift, ball, h, hb, hw, square, newton

LO=F('14.24')
HI=F('14.36')
LEFT=F('14.298713824150')
RIGHT=F('14.298713824153')
RETURN_LEFT=F('14.879019351554')
RETURN_RIGHT=F('14.879019351557')
RN= '1e-24'

def vel(s,b): return -hb(s,b)/(180*hw(s,b))

def hbb(w,b): return w*(w+1)*h(w+2,b)

def slopes(box,span,second):
    # g = d log|q-p| / dh = Re int_0^1 v_w((1-s)p+sq,b) ds.
    # Its derivative along the two transported points also uses d((1-s)p+sq)/dh.
    n=3 if second else 2
    tc=acb_series([box.mid(),1],n+2)
    t=acb_series([box,1],n+2)
    a,c=h(t,span),hb(t,span)
    a0,c0=h(tc,span.mid()),hb(tc,span.mid())
    c2=hbb(t,span)
    dw,db=box-box.mid(),span-span.mid()
    def coeff(A0,A,Ab,i):
        return A0[i]+(i+1)*A[i+1]*dw+Ab[i]*db
    a_w=acb_series([(i+1)*coeff(a0,a,c,i+1) for i in range(n)],n)
    if a_w[0].contains(0) or not a_w[0].is_finite(): return arb('nan')
    cs=acb_series([coeff(c0,c,c2,i) for i in range(n)],n)
    v=-cs/(180*a_w)
    if not second: return v[1].real
    c_w=acb_series([(i+1)*coeff(c0,c,c2,i+1) for i in range(n)],n)
    c3=t*(t+1)*hb(t+2,span)
    c20=hbb(tc,span.mid())
    c2s=acb_series([coeff(c20,c2,c3,i) for i in range(n)],n)
    v_b=-(c2s-cs*(c_w/a_w))/(180*a_w)
    # v[0] encloses both velocities and their convex combinations.
    return (v_b[1]/180+2*v[2]*v[0]).real

def certified_cell(nodes,levels,l,r,region):
    lb,rb=shift(l),shift(r)
    span=lb.union(rb)
    mid,half=span.mid(),span.rad()
    rad=arb(RN)
    center=newton(nodes[0],mid,levels[0],4)
    der=hw(center,mid)
    d=der.mid()
    hmid=h(center,mid)
    pmax=max(abs(hmid-lev).upper() for lev in levels)
    res=pmax+half*abs(hb(center,span))
    radius=max(8*rad,(3*res/abs(d)).upper(),
               (2*max(abs(center-p).upper() for p in nodes)+4*rad).upper())
    if radius>arb('.15'): return None
    box=square(center,radius)
    hww=2*h(acb_series([box,1],3),span)[2]
    hwb=hb(acb_series([center,1],2),span)[1]
    k=(abs(d-der)+radius*abs(hww)+half*abs(hwb))/abs(d)
    if not (k<1 and res/abs(d)+k*radius<radius): return None
    ends=tuple(newton(center,rb,c,4) for c in levels)
    for node,end,c in zip(nodes,ends,levels):
        assert abs(center-node)+rad<radius
        if not (abs(center-end)+rad<radius and abs((h(end,rb)-c)/d)+k*rad<rad): return None
    order2=region=='falling slope'
    bound=slopes(box,span,order2)
    if not (bound>0 if region=='grow' else bound<0): return None
    return ends,bound

def slope_at_end(nodes,angle):
    b=shift(angle)
    p,q=[square(x,arb(RN)) for x in nodes]
    return ((vel(q,b)-vel(p,b))/(q-p)).real

def run():
    ctx.prec,ctx.cap=176,6
    states,levels=starts()
    counts=[]
    angles={}; factors={}
    for lo,hi,cat in [(START,LO,'grow'),(LO,LEFT,'falling slope'),(LEFT,RIGHT,'falling slope'),
                      (RIGHT,HI,'falling slope'),(HI,RETURN_LEFT,'shrink'),
                      (RETURN_LEFT,RETURN_RIGHT,'shrink'),(RETURN_RIGHT,END,'shrink')]:
        queue=[(lo,hi)]
        steps=0
        bound=None
        while queue:
            l,r=queue.pop()
            result=certified_cell(states,levels,l,r,cat)
            if result is None:
                assert r-l>F(1,2**30)
                m=(l+r)/2
                queue.extend([(m,r),(l,m)])
                continue
            states,nxt=result
            bound=nxt if bound is None else bound.union(nxt)
            steps+=1
        counts.append([str(float(lo)),str(float(hi)),cat,steps,[bound.lower().str(8),bound.upper().str(8)]])
        print(counts[-1],flush=True)
        angles[str(float(hi))]=slope_at_end(states,hi).str(16)
        factors[str(float(hi))]=(abs(square(states[1],arb(RN))-square(states[0],arb(RN)))/ball(GAP)).str(18)
        if hi==LEFT: assert slope_at_end(states,hi)>0
        if hi==RIGHT: assert slope_at_end(states,hi)<0
        if hi==RETURN_LEFT: assert arb(factors[str(float(hi))])>1
        if hi==RETURN_RIGHT: assert arb(factors[str(float(hi))])<1
    assert arb(factors[str(float(END))])<1
    peak_lo=arb(factors[str(float(LEFT))])
    peak_hi=peak_lo*(ball(RIGHT-LEFT)*arb(angles[str(float(LEFT))])).exp()
    return dict(bits=ctx.prec,first_angle=str(START),final_angle=str(END),intervals=counts,
                log_gap_slopes_at_right_ends=angles,finite_gap_over_initial_at_right_ends=factors,
                unique_peak_degrees=[str(float(LEFT)),str(float(RIGHT))],maximum_normalized_gap=peak_lo.union(peak_hi).str(20),
                first_return_to_initial_gap_degrees=[str(float(RETURN_LEFT)),str(float(RETURN_RIGHT))],minimum='right endpoint')

if __name__=='__main__':
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE)
    args=parser.parse_args()
    args.output.mkdir(exist_ok=True,parents=True)
    out=run()
    (args.output/'neighbor_proof.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
