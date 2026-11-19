"""A transverse double visit of the sixth branch at two distinct clockwise angles."""
import argparse
import json

from flint import arb, ctx

from verify import BASE, F, HERE, Branch, ball, jets, source_root


def parameter(angle):
    return BASE+angle/180


def inverse_midpoint(u,v):
    # Derivative of w(h1)-w(h2) in real coordinates has columns u,-v.
    a,b,c,d=u.real,-v.real,u.imag,-v.imag
    det=a*d-b*c
    inv=[x.mid() for x in (d/det,-b/det,-c/det,a/det)]
    assert not (inv[0]*inv[3]-inv[1]*inv[2]).contains(0)
    return inv


def apply(matrix,z):
    a,b,c,d=matrix
    return a*z.real+b*z.imag,c*z.real+d*z.imag


def measure(archive):
    ctx.prec,ctx.cap=192,3
    branch=Branch(archive)
    angles=[F('10.02'),F('13.60')]
    # Newton only selects the rational center for the following enclosure.
    for _ in range(5):
        (x,u,_),(y,v,_)=[branch.node_values(parameter(h)) for h in angles]
        steps=apply(inverse_midpoint(u,v),x-y)
        angles=[F((ball(h)-d).mid().str(27,radius=False)) for h,d in zip(angles,steps)]

    (x,u,_),(y,v,_)=[branch.node_values(parameter(h)) for h in angles]
    pre=inverse_midpoint(u,v)
    step=apply(pre,x-y)
    radius=F(1,10**19)
    positions=[]
    velocities=[]
    spans=[]
    for h in angles:
        a,b=parameter(h-radius),parameter(h+radius)
        w=branch.enclose(a,b)
        speed,_=jets(w,ball(a).union(ball(b)))
        positions.append(w)
        velocities.append(speed)
        spans.append(ball(h-radius).union(ball(h+radius)))
    assert spans[0]<spans[1]

    # Fixed point of h -> h - pre*(w(h1)-w(h2)) on the full square.
    # Each column enclosure uses the branch jet on the entire angle interval.
    r1,r2=apply(pre,velocities[0])
    s1,s2=apply(pre,-velocities[1])
    row_norms=[abs(1-r1)+abs(s1),abs(r2)+abs(1-s2)]
    assert all(q<1 and abs(d)+q*ball(radius)<ball(radius) for q,d in zip(row_norms,step))

    x,y=positions
    v1,v2=velocities
    assert x.real.overlaps(y.real) and x.imag.overlaps(y.imag)
    to_deg=180/arb.pi()
    turn=(v1.conjugate()*v2).arg()*to_deg
    determinant=(v1.conjugate()*v2).imag
    assert determinant<0 and 90<abs(turn) and abs(turn)<180
    values=dict(alpha1=spans[0],alpha2=spans[1],sigma=x.real.intersection(y.real),T=x.imag.intersection(y.imag),
                sigma1=v1.real,T1=v1.imag,sigma2=v2.real,T2=v2.imag,
                direction1_deg=v1.arg()*to_deg,direction2_deg=v2.arg()*to_deg,
                oriented_angle_deg=turn,acute_angle_deg=180-abs(turn),
                slope1=v1.imag/v1.real,slope2=v2.imag/v2.real,tangent_determinant=determinant)
    return dict(source_sha256=branch.digest,precision_bits=ctx.prec,
                proof='strict contraction of preconditioned two-parameter difference on angle box',
                box_centers_degrees=[str(h) for h in angles],box_radius_degrees=str(radius),
                row_norm_upper=[q.abs_upper().str(15) for q in row_norms],
                midpoint_step_bounds=[d.str(15) for d in step],
                bounds={k:v.str(19) for k,v in values.items()},mid={k:float(v.mid()) for k,v in values.items()})


if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run with assertions enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=type(HERE))
    parser.add_argument('--output',type=type(HERE),default=HERE/'revisit.json')
    parser.add_argument('--compare',type=type(HERE))
    args=parser.parse_args()
    result=measure(source_root(args.archive))
    if args.compare:
        old=json.loads(args.compare.read_bytes())
        assert old['source_sha256']==result['source_sha256'] and old['precision_bits']==result['precision_bits']
        assert old['bounds'].keys()==result['bounds'].keys()
        for k,s in result['bounds'].items():
            assert arb(s).overlaps(arb(old['bounds'][k])),k
            assert abs(result['mid'][k]-old['mid'][k])<1e-10,k
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(result['mid'])
