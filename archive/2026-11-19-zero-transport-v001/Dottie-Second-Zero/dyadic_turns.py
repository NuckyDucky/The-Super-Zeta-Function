"""Isolate both extrema of the real part on the already certified dyadic branch."""
from fractions import Fraction as F
import json
from flint import arb,acb,acb_series,ctx
from dyadic_geometry import HERE,parsed,tangent
from arithmetic_braid import ball,complex_record,shrink_root
from arithmetic_reference import derivative_w,derivative_angle
from arithmetic_holdout_replay import centered_tube

def jet(w,b):
    v=acb_series([w,1],3)
    pi=arb.pi()
    factor=(-v*pi.log()).exp()
    f=(v.zeta(b)+v.zeta(1-b))*factor
    fb=-v*((v+1).zeta(b)-(v+1).zeta(1-b))*factor
    fbb=w*(w+1)*(-w*pi.log()).exp()*((w+2).zeta(b)+(w+2).zeta(1-b))
    vel=-fb[0]/f[1]
    acc=-(fbb+2*fb[1]*vel+2*f[2]*vel*vel)/f[1]
    return vel.real,acc.real

def run():
    ctx.prec=224
    ctx.cap=3
    pts=json.loads((HERE/'dyadic_continuation.json').read_text())['checkpoints']
    r=arb('1e-16')
    prove=0
    zones=[(70,73,-1),(180,183,1)]
    signs=[]
    def sign_at(p,b):
        return (arb.pi()*derivative_angle(p,ball(b))/derivative_w(p,ball(b))).real
    for j in range(256):
        a,b=(F(pts[i]['shift']) for i in (j,j+1))
        start=parsed(pts[j]['zero'])
        node=start.mid()
        assert abs(start-node)<r
        local=next((h for l,u,h in zones if l<=j<u),0)
        want=(1 if j<70 or j>=183 else -1)
        todo=[(a,b,0)]
        while todo:
            l,u,depth=todo.pop()
            res=centered_tube(node,r,l,u)
            if res is not None:
                end,k,rad,c=res
                square=c+acb(arb(0,rad),arb(0,rad)); span=ball(l).union(ball(u))
                vel,acc=jet(square,span)
                if local:
                    good=local*acc>0
                else:
                    startvel=sign_at(node+acb(arb(0,r),arb(0,r)),l)
                    # Real fundamental theorem of calculus along the simple branch.
                    vu=startvel + acc*arb(0).union(ball(u-l))
                    good=want*vu>0
                if good:
                    node=end;prove+=1
                    continue
            assert depth<25,(j,l,u)
            m=(l+u)/2
            todo.extend(((m,u,depth+1),(l,m,depth+1)))
        assert abs(node-parsed(pts[j+1]['zero']))<2*r
    bounds=[]
    for j,orient in [(71,-1),(181,1)]:
        a,b=F(pts[j]['shift']),F(pts[j+1]['shift'])
        n=parsed(pts[j]['zero']).mid()
        assert orient*sign_at(parsed(pts[j]['zero']),a)<0
        assert orient*sign_at(parsed(pts[j+1]['zero']),b)>0
        # Intersect the relevant unique branch with narrow nested intervals.
        for _ in range(12):
            m=(a+b)/2
            probe=centered_tube(n,r,a,m)
            if probe is None: break
            e=probe[0];sd=orient*sign_at(e+acb(arb(0,r),arb(0,r)),m)
            assert not sd.contains(0)
            if sd>0: b=m
            else: a=m; n=e
        full=centered_tube(n,r,a,b)
        assert full is not None
        _,_,rad,c=full
        bounds.append(dict(kind='maximum' if orient<0 else 'minimum',
                           theta_degrees=[str(float((F(1,2)-b)*180)),str(float((F(1,2)-a)*180))],
                           zero=complex_record(c+acb(arb(0,rad),arb(0,rad)))))
    return dict(precision_bits=ctx.prec,unique_horizontal_extrema=bounds,certified_subintervals=prove)
if __name__=='__main__':
    d=run()
    (HERE/'dyadic_turns.json').write_text(json.dumps(d,indent=2)+'\n')
    print(d)
