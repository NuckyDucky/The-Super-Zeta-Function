"""Compare the four sixth-branch folds using the same clockwise degree unit."""
from pathlib import Path
from fractions import Fraction as F
import sys
import json
from flint import ctx,arb

HERE=Path(__file__).resolve().parent
OUTPUTS=HERE.parent
sys.path.insert(0,str(OUTPUTS/'Dottie-Sixth-Passes'/'compute'))
from verify import Branch,BASE,ball
from turning import partials,enclosure


def param(h): return BASE+h/180


def intervals(br,hb):
    h,j=map(F,(str(hb.lower().fmpq()),str(hb.upper().fmpq())))
    b0,b1=param(h),param(j)
    return br.enclose(b0,b1),ball(b0).union(ball(b1))


def derivatives(w,b):
    D=partials(w,b,3)
    return jets_from_partials(D)


def jets_from_partials(D):
    v=-D[0,1]/D[1,0]
    a=-(D[2,0]*v*v+2*D[1,1]*v+D[0,2])/D[1,0]
    j=-(D[3,0]*v**3+3*D[2,1]*v*v+3*D[1,2]*v+D[0,3]+3*(D[2,0]*v+D[1,1])*a)/D[1,0]
    return v/180,a/180**2,j/180**3


def jerk_bound(br,h,acceleration,limit):
    # Taylor's integral remainder gives a relative error <= M*d/(3*|T''|).
    # Here M bounds |T'''| continuously throughout the whole radius, d=.01°.
    left=param(F(str(h.lower().fmpq()))-F(1,100))
    right=param(F(str(h.upper().fmpq()))+F(1,100))
    node=br.at(left)
    todo=[(left,right)]
    worst=arb(0)
    count=0
    while todo:
        l,r=todo.pop()
        proof=br.centered_tube(node,br.radius,l,r)
        if proof is not None:
            end,_,rad,c=proof
            from verify import square
            span=ball(l).union(ball(r))
            bd=partials(square(c,rad),span,3)
            mid=partials(c,ball((l+r)/2),2)
            for n in (2,1):
                for j in range(n+1):
                    i=n-j
                    err=(rad*abs(bd[i+1,j])+ball((r-l)/2)*abs(bd[i,j+1])).upper()
                    bd[i,j]=square(mid[i,j],err)
            third=jets_from_partials(bd)[2]
            rel=abs(third.imag)/(300*abs(acceleration))
            if rel.is_finite() and rel<limit:
                worst=max(worst,rel.upper())
                node=end
                count+=1
                continue
        assert r-l>F(1,10**15)
        m=(l+r)/2
        todo.extend([(m,r),(l,m)])
    return dict(radius_degrees="1/100",max_relative_error_to_quadratic=worst.str(14),cells=count)


def record(br):
    intervals_of_h=[('6.97908627','6.97908632',-1),('7.52412075','7.52412082',1),
                    ('10.95490542','10.95490549',-1),('13.40917355','13.40917366',1)]
    names=['Lower crest','Lower trough','Upper crest','Upper trough']
    folds=[]
    values=[]
    for idx,((l,r,s),name) in enumerate(zip(intervals_of_h,names)):
        ev=br.event('heightfold',l,r,s)['bounds']
        h=arb(ev['alpha'])
        z,B=intervals(br,h)
        v,a,j=derivatives(z,B)
        assert v.imag.contains(0)
        T=z.imag
        values.append((h,T))
        coeff=a.imag/2
        geom=coeff/v.real**2
        offsets=[]
        for offset in [-.1,-.05,-.01,.01,.05,.1]:
            dh=ball(F(str(offset)))
            pos,_=intervals(br,h+dh)
            rise=pos.imag-T
            model=coeff*dh**2
            offsets.append(dict(dh=offset,height_change=rise.str(16),
                                quadratic_height_change=model.str(16),
                                relative_error_to_quadratic=((rise-model)/abs(model)).str(14)))
        radii=[.004,.04,.009,.009]
        uniform=jerk_bound(br,h,a.imag,arb(str(radii[idx])))
        samples=[]
        for k in range(-20,21):
            dh=ball(F(k,200))
            pos,_=intervals(br,h+dh)
            samples.append([k/200,float(((pos.imag-T)/(coeff/100)).mid())])
        folds.append(dict(name=name,h=h.str(20),sigma=z.real.str(20),T=T.str(20),
            sideways_velocity=v.real.str(16),height_acceleration=a.imag.str(16),height_jerk=j.imag.str(16),
            quadratic_angle=coeff.str(16),quadratic_physical=geom.str(16),offsets=offsets,
            uniform_quadratic_remainder=uniform,local_plot=samples))
    arcs=[]
    for i in (0,2):
        h0,T0=values[i]
        h1,T1=values[i+1]
        width=h1-h0
        drop=T0-T1
        samples=[]
        for k in range(1,100):
            t=ball(F(k,100))
            z,_=intervals(br,h0+t*width)
            y=(z.imag-T1)/drop
            smooth=1-3*t**2+2*t**3
            samples.append(dict(u=k/100,profile=y.str(16),difference=(y-smooth).str(16)))
        arcs.append(dict(clockwise_width=width.str(16),height_drop=drop.str(16),samples=samples))
    return dict(precision_bits=ctx.prec,source_sha256=br.digest,folds=folds,descending_arcs=arcs)


if __name__=='__main__':
    ctx.prec,ctx.cap=192,4
    results=record(Branch(OUTPUTS))
    (HERE/'fold-shapes.json').write_text(json.dumps(results,indent=2)+'\n')
    for item in results['folds']:
        print(item['name'],item['quadratic_angle'],item['quadratic_physical'],item['height_jerk'],[i['relative_error_to_quadratic'] for i in item['offsets']],flush=True)
    for arc in results['descending_arcs']:
        print(arc['clockwise_width'],arc['height_drop'],[arc['samples'][i]['profile'] for i in (24,49,74)],flush=True)
