"""Certified chart of the first Hurwitz summand along the sixth simple branch."""
from pathlib import Path
import argparse
import json
import sys
from flint import acb, acb_series, arb, ctx

HERE = Path(__file__).resolve().parent
from layout import PREVIOUS, TRANSPORT, OUTPUT
sys.path.insert(0, str(PREVIOUS))
from verify import BASE, F, Branch, ball, square
from revisit import inverse_midpoint, apply


def parameter(h):
    return BASE+h/180


def slope(w,b):
    z=acb_series([w,1],2)
    A,B=z.zeta(b),z.zeta(1-b)
    Ab=-w*(w+1).zeta(b)
    Bb=w*(w+1).zeta(1-b)
    return (Ab*B[1]-Bb*A[1])/(180*(A[1]+B[1]))


def evaluate(br,h):
    b=parameter(h)
    w=square(br.at(b),br.radius)
    return w,w.zeta(ball(b)),slope(w,ball(b))


def crossing(br):
    hs=[F('9.684'),F('14.732')]
    for _ in range(5):
        (_,a,u),(_,b,v)=[evaluate(br,h) for h in hs]
        change=apply(inverse_midpoint(u,v),a-b)
        hs=[F((ball(h)-d).mid().str(27,radius=False)) for h,d in zip(hs,change)]
    (_,a,u),(_,b,v)=[evaluate(br,h) for h in hs]
    pre=inverse_midpoint(u,v)
    steps=apply(pre,a-b)
    radius=F(1,10**18)
    boxes=[]
    for h in hs:
        l,r=parameter(h-radius),parameter(h+radius)
        w=br.enclose(l,r)
        B=ball(l).union(ball(r))
        boxes.append((w,w.zeta(B),slope(w,B)))
    (w1,s1,v1),(w2,s2,v2)=boxes
    a,b=apply(pre,v1)
    c,d=apply(pre,-v2)
    k=max((abs(1-a)+abs(c)).upper(),(abs(b)+abs(1-d)).upper())
    assert k<1 and all(abs(s)+k*ball(radius)<ball(radius) for s in steps)
    assert not w1.overlaps(w2)
    assert s1.overlaps(s2)
    det=(v1.conjugate()*v2).imag
    assert not det.contains(0)
    fields=dict(A_real=s1.real.intersection(s2.real),A_imag=s1.imag.intersection(s2.imag),
                sigma1=w1.real,T1=w1.imag,sigma2=w2.real,T2=w2.imag,tangent_determinant=det)
    for i,h in enumerate(hs,1):
        fields[f"h{i}"]=ball(h-radius).union(ball(h+radius))
    return dict(bounds={k:v.str(19) for k,v in fields.items()},centers=[str(h) for h in hs],
                box_radius_degrees=str(radius),contraction=k.str(12))


def partials(c,r,m,width,sign):
    # The second derivatives bound the variation of each first derivative
    # from the central point throughout the verified zero disk.
    z=square(c,r)
    t=acb_series([z,1],3)
    u=acb_series([c,1],2)
    x=ball(m) if sign==1 else 1-ball(m)
    span=x+arb(0,width)
    u0=u.zeta(x)
    dww=2*t.zeta(span)[2]
    dwb=(-sign*t*(t+1).zeta(span))[1]
    dbb=z*(z+1)*(z+2).zeta(span)
    return (square(u0[1],(r*abs(dww)+width*abs(dwb)).upper()),
            square(-sign*c*(c+1).zeta(x),(r*abs(dwb)+width*abs(dbb)).upper()))


def imaginary_axis(br):
    l,r=F('12.18'), F('12.66')
    assert evaluate(br,l)[1].real>0 and evaluate(br,r)[1].real<0
    for _ in range(47):
        m=(l+r)/2
        x=evaluate(br,m)[1].real
        assert not x.contains(0)
        if x>0: l=m
        else: r=m
    a,b=parameter(l),parameter(r)
    w=br.enclose(a,b)
    span=ball(a).union(ball(b))
    value=w.zeta(span)
    v=slope(w,span)
    assert value.real.contains(0) and value.imag>6 and v.real<0
    return dict(h=ball(l).union(ball(r)).str(20),A_real="0",A_imag=value.imag.str(20),
                dA_real_dh=v.real.str(16))


def interval_velocity(c,r,l,b):
    m=(l+b)/2
    width=ball((b-l)/2)
    aw,ab=partials(c,r,m,width,1)
    bw,bb=partials(c,r,m,width,-1)
    return (ab*bw-bb*aw)/(180*(aw+bw))


def full_chart(br,record):
    node=br.at(BASE)
    pieces=[]
    lo,hi=arb(10),arb(0)
    for a,b in zip(br.knots,br.knots[1:]):
        todo=[(a,b)]
        while todo:
            l,r=todo.pop()
            cert=br.centered_tube(node,br.radius,l,r)
            if cert is not None:
                end,_,rad,c=cert
                v=interval_velocity(c,rad,l,r)
                h0,h1=180*(l-BASE),180*(r-BASE)
                if (v.is_finite() and abs(v)>arb(1)/10 and abs(v)<6 and
                    max(v.real.rad(),v.imag.rad())<arb(2)/10 and h1-h0<F(1,25)):
                    lo=min(lo,abs(v).lower())
                    hi=max(hi,abs(v).upper())
                    # Mean value for a real parameter and complex output.
                    start=square(node,br.radius).zeta(ball(l))
                    stop=square(end,br.radius).zeta(ball(r))
                    displacement=v*ball(h1-h0).union(arb(0))
                    from_left=start+displacement
                    from_right=stop-displacement
                    value=acb(from_left.real.intersection(from_right.real),
                              from_left.imag.intersection(from_right.imag))
                    pieces.append((h0,h1,value,v,square(c,rad)))
                    node=end
                    continue
            assert r-l>F(1,2**38)
            mid=(l+r)/2
            todo.extend([(mid,r),(l,mid)])
        assert abs(node-br.at(b))+br.radius < arb('1e-9')
        assert br.disk_check(node,arb('1e-9'),ball(b))[2]

    # If all cells from i through j share a strictly monotone projection,
    # distinct parameters across that range give distinct summand values.
    ends=[]
    last=[len(pieces)]*4
    for i in reversed(range(len(pieces))):
        v=pieces[i][3]
        signs=(v.real>0,v.real<0,v.imag>0,v.imag<0)
        for j,direction in enumerate(signs):
            if not direction: last[j]=i
        ends.append(max(last))
        assert max(last)>i
    ends.reverse()
    ambiguous=[]
    for i,(_,_,value,_,w) in enumerate(pieces):
        for j in range(ends[i],len(pieces)):
            if not value.overlaps(pieces[j][2]): continue
            assert not w.overlaps(pieces[j][4]),(i,j,'joint coordinate ambiguity')
            ambiguous.append((i,j))
    assert ambiguous
    # The remaining box pairs are all in a single ordered rectangle. The
    # preconditioned difference has derivative norm <1 throughout its hull.
    # Consequently two fixed points there would violate the Lipschitz bound.
    i0,i1=min(i for i,j in ambiguous),max(i for i,j in ambiguous)
    j0,j1=min(j for i,j in ambiguous),max(j for i,j in ambiguous)
    assert i1<j0
    p,q=(F(h) for h in record['centers'])
    assert pieces[i0][0]<p<pieces[i1][1] and pieces[j0][0]<q<pieces[j1][1]
    pre=inverse_midpoint(evaluate(br,p)[2],evaluate(br,q)[2])
    c1=[apply(pre,row[3]) for row in pieces[i0:i1+1]]
    c2=[apply(pre,-row[3]) for row in pieces[j0:j1+1]]
    k=max(max(abs(1-x).upper() for x,y in c1)+max(abs(u).upper() for u,v in c2),
          max(abs(y).upper() for x,y in c1)+max(abs(1-v).upper() for u,v in c2))
    assert k<1,k
    return dict(precision_bits=ctx.prec,source_sha256=br.digest,range_degrees=[0,15],
        cells=len(pieces), speed_enclosure=[lo.str(12),hi.str(12)], remaining_box_pairs=len(ambiguous),
        possible_collision_hulls_degrees=[[str(pieces[i0][0]),str(pieces[i1][1])],
                                           [str(pieces[j0][0]),str(pieces[j1][1])]],
        uniqueness_on_collision_hull_lipschitz_upper=k.upper().str(12), transverse_double_points=1,
        joint_coordinate_is_injective=True)


if __name__=='__main__':
    if not __debug__: raise RuntimeError('Keep assertions enabled')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',type=Path,default=TRANSPORT)
    p.add_argument('--full',action='store_true',help='also certify the whole 15 degree branch')
    args=p.parse_args()
    ctx.cap,ctx.prec=3,192
    br=Branch(args.archive)
    record=crossing(br)
    (OUTPUT/'chart-crossing.json').write_text(json.dumps(record,indent=2)+'\n')
    (OUTPUT/'imaginary-axis.json').write_text(json.dumps(imaginary_axis(br),indent=2)+'\n')
    print(record,flush=True)
    if args.full:
        global_result=full_chart(br,record)
        (OUTPUT/'chart.json').write_text(json.dumps(global_result,indent=2)+'\n')
        print(global_result,flush=True)
