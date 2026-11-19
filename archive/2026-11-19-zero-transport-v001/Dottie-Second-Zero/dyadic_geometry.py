"""Verify which side of the critical line the primary path occupies along the full arc."""
from pathlib import Path
import json
from fractions import Fraction
from flint import acb, acb_series, arb, ctx
from dyadic_continuation import HERE
from arithmetic_braid import ball, complex_record
from arithmetic_reference import reference, derivative_w, derivative_angle
from arithmetic_holdout_replay import centered_tube

def parsed(box):
    return acb(arb(box['real']), arb(box['imag']))

def tangent(center, radius, a, b):
    d=acb(arb(0,radius),arb(0,radius))
    square=center+d
    mid=ball((a+b)/2)
    width=ball((b-a)/2)
    span=ball(a).union(ball(b))
    pi=arb.pi()
    # Enclose first derivatives by the mean-value estimate in w and b.
    v=acb_series([square,1],3)
    dww=2*((v.zeta(span)+v.zeta(1-span))*(-v*pi.log()).exp())[2]
    v=acb_series([square,1],2)
    dwb=(-v*((v+1).zeta(span)-(v+1).zeta(1-span))*(-v*pi.log()).exp())[1]
    dbb=square*(square+1)*(pi.log()*(-square)).exp()*((square+2).zeta(span)+(square+2).zeta(1-span))
    dw_radius=(radius*abs(dww)+width*abs(dwb)).upper()
    db_radius=(radius*abs(dwb)+width*abs(dbb)).upper()
    err=lambda r: acb(arb(0,r),arb(0,r))
    dw=derivative_w(center,mid)+err(dw_radius)
    db=-pi*derivative_angle(center,mid)+err(db_radius)
    return -db/dw

def run():
    ctx.prec=224
    ctx.cap=3
    points=json.loads((HERE/'dyadic_continuation.json').read_text())['checkpoints']
    disk_radius=arb('1e-16')
    max_segments=25000
    segments=0
    min_height_slope=arb('1e6')
    max_height_slope=arb(0)
    edge_positive=0
    for i in range(len(points)-1):
        start=parsed(points[i]['zero'])
        node=start.mid()
        assert abs(start-node)<disk_radius
        left,right=[Fraction(p['shift']) for p in points[i:i+2]]
        pending=[(left,right,0)]
        while pending:
            a,b,d=pending.pop()
            result=centered_tube(node,disk_radius,a,b)
            accepted=False
            if result is not None:
                end,k,r,center=result
                velocity=tangent(center,r,a,b)
                if velocity.is_finite() and velocity.imag>0:
                    lower=center.real-r>0
                    upper=center.real+r<arb(1)/2
                    # Start is exactly on Re=0. The independently classified
                    # endpoint is exactly on Re=1/2. Interior ends use disks.
                    if not lower and velocity.real>0:
                        lower=(a==Fraction(1,6) or node.real-disk_radius>0)
                    if not upper and velocity.real>0:
                        upper=(b==Fraction(1,4) or end.real+disk_radius<arb(1)/2)
                    if lower and upper:
                        edge_positive+=int(center.real-r<=0 or center.real+r>=arb(1)/2)
                        min_height_slope=min(min_height_slope,velocity.imag.lower())
                        max_height_slope=max(max_height_slope,velocity.imag.upper())
                        accepted=True
                        node=end
                        segments+=1
            if not accepted:
                assert d<30,(a,b,node)
                h=(a+b)/2
                pending.extend(((h,b,d+1),(a,h,d+1)))
            assert segments<max_segments
        # Original and replay certificates describe the same branch by uniqueness:
        # both start in the archived disk and each branch is continuous.
        assert abs(node-parsed(points[i+1]['zero']))<2*disk_radius
    # Present the clockwise incoming derivative in degrees: b'=1/180.
    endpoint=parsed(points[-1]['zero'])
    w_end=endpoint.mid()
    rad=abs(endpoint-w_end).upper()
    incoming=tangent(w_end,rad,Fraction(1,4),Fraction(1,4))/180
    return dict(precision_bits=ctx.prec,segments=segments,
                source='dyadic_continuation.json',
                height_slope_per_unit_b=[min_height_slope.str(15),max_height_slope.str(15)],
                segments_using_edge_tangents=edge_positive,
                open_strip_condition='0 < real(w) < 1/2 on 1/6 < b < 1/4, using exact endpoint symmetry',
                terminal_slope_per_clockwise_degree=complex_record(incoming))
if __name__=='__main__':
    results=run()
    (HERE/'dyadic_geometry.json').write_text(json.dumps(results,indent=2)+'\n')
    print(results)
