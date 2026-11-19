"""Build one plot for every branch ending at Riemann zeros 1..10 and the pictured blue branch.

Using Python 3.12 / python-flint 0.9.0: run trace.py for 8, 9 and 10, then this file.
The optional --bounds stage encloses the global horizontal extrema over every cell.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
OUTPUTS = HERE.parents[1]
sys.path.insert(0, str(OUTPUTS/'Dottie-Second-Zero'))
from dyadic_geometry import parsed, tangent
from arithmetic_braid import ball, shrink_root
from arithmetic_reference import derivative_angle, derivative_w, disk_check
from arithmetic_holdout_replay import centered_tube

FILES = {
    1: ('Dottie-Off-Axis-Return/arithmetic_braid_lattice.json', '4πi/log 3'),
    2: ('Dottie-Second-Zero/dyadic_continuation.json','4πi/log 2'),
    3: ('Dottie-Third-Zero/sweep_1.json','ρ2'),
    4: ('Dottie-Forward-Iteration/sweep_1.json','ρ3'),
    5: ('Dottie-Transport-Reversibility/rho5-replay.json','10πi/log 3'),
    6: ('Dottie-Transport-Reversibility/rho6-replay.json','12πi/log 3'),
    7: ('Dottie-Forward-Iteration/sweep_3.json','8πi/log 2'),
    8: ('Dottie-Turn-Geometry/ten/backwards-8.json','ρ6'),
    9: ('Dottie-Turn-Geometry/ten/backwards-9.json','ρ7'),
    10: ('Dottie-Turn-Geometry/ten/backwards-10.json','ρ8'),
    0: ('Dottie-Forward-Iteration/sweep_2.json','ρ4'),
}

def get_points(index):
    record = json.loads((OUTPUTS/FILES[index][0]).read_bytes())
    data = (record.get('paths') or [record])[0]
    pts = sorted([(F(p.get('shift') or p['b']),parsed(p['zero'])) for p in data['checkpoints']])
    for rank, row, b in [(index,pts[-1],F(1,4)), ({8:6,9:7,10:8}.get(index),pts[0],F(1,6))]:
        if rank:
            center = row[1].mid()
            assert abs(acb.zeta_zero(rank)-center)<arb('1e-9')
            assert disk_check(center,arb('1e-9'),ball(b))[2]
    return pts

def derivative(z,b):
    return derivative_angle(z,ball(b))/derivative_w(z,ball(b))

def fmt(x):
    return round(float(x.mid()),12)

def row(b,z):
    v = derivative(z,b)
    return [round(float(180*(b-F(1,6))),12), fmt(z.real),fmt(z.imag),fmt(v.real),fmt(v.imag)]

def resolve_turn(left,right):
    a,za = left
    b,zb = right
    va = derivative(za,a).real
    assert not va.contains(0)
    for _ in range(32):
        mid = (a+b)/2
        z = shrink_root(((za+zb)/2).mid(),ball(mid),4)
        if derivative(z,mid).real*va > 0:
            a,za = mid,z
        else:
            b,zb = mid,z
    mid = (a+b)/2
    z = shrink_root(((za+zb)/2).mid(),ball(mid),4)
    return row(mid,z)

def geometry(index):
    pts = get_points(index)
    samples = [row(b,z) for b,z in pts]
    forts = [resolve_turn(pts[j],pts[j+1]) for j in range(len(pts)-1)
             if samples[j][3]*samples[j+1][3]<0]
    candidates = [samples[0],samples[-1],*forts]
    return dict(id=f'rho{index}' if index else 'blue',ordinal=index or None,
                start_label=FILES[index][1],end_label=f'ρ{index}' if index else '8πi/log 2',
                source=FILES[index][0], samples=samples, extrema=dict(
                    min_real=min(candidates,key=lambda p:p[1]),max_real=max(candidates,key=lambda p:p[1]),
                    interior_horizontal_turns=forts))

def certify_bounds(curve):
    pts=get_points(curve['ordinal'] or 0)
    xmin=F(str(curve['extrema']['min_real'][1]))
    xmax=F(str(curve['extrema']['max_real'][1]))
    delta=F(1,10**7)
    low=ball(xmin-delta)
    high=ball(xmax+delta)
    node_radius=arb('1e-13')
    accepted=0
    for (a0,left),(b0,right) in zip(pts,pts[1:]):
        assert abs(left-left.mid())<node_radius
        node=left.mid()
        pending=[(a0,b0,0)]
        while pending:
            a,b,d=pending.pop()
            result=centered_tube(node,node_radius,a,b)
            if result is not None:
                end,_,r,c=result
                gaussian_disk=c.real+arb(0,r)
                fits = gaussian_disk>low and gaussian_disk<high
                if not fits:
                    v=tangent(c,r,a,b).real
                    zero_to_step=arb(0).union(ball(b-a))
                    span=(node.real+arb(0,node_radius))+zero_to_step*v
                    fits=span>low and span<high
                if fits:
                    node=end
                    accepted+=1
                    continue
            assert d<40,(curve['id'],a,b)
            mid=(a+b)/2
            pending.extend(((mid,b,d+1),(a,mid,d+1)))
        assert abs(node-right)<2*node_radius
    attained=[]
    for x in ('min_real','max_real'):
        rr=curve['extrema'][x]
        b=F(1,6)+F(str(rr[0]))/180
        seed=acb(arb(str(rr[1])),arb(str(rr[2])))
        lo=next(((a,z) for a,z in reversed(pts) if a<=b),None)
        assert lo
        a,node=lo[0],lo[1].mid()
        if b!=a:
            sub=[(a,b)]
            while sub:
                start,stop=sub.pop()
                tube=centered_tube(node,node_radius,start,stop)
                if tube:
                    node=tube[0]
                    continue
                split=(start+stop)/2
                sub.extend(((split,stop),(start,split)))
        assert abs(node-seed)<arb('1e-9')
        assert abs(node.real-ball(F(str(rr[1]))))+node_radius<ball(delta)
        attained.append(str(b))
    return dict(min_real=[float(xmin-delta),float(xmin+delta)],
                max_real=[float(xmax-delta),float(xmax+delta)],certified_cells=accepted,
                witness_shifts=attained)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bounds',action='store_true')
    parser.add_argument('--index',type=int)
    parser.add_argument('--assemble',action='store_true')
    args=parser.parse_args()
    ctx.prec,ctx.cap=192,3
    if args.index is not None:
        curves=[geometry(args.index)]
    elif args.assemble:
        curves=[json.loads((HERE/f'summary-{i}.json').read_bytes()) for i in FILES]
    else:
        curves=[geometry(i) for i in FILES]
    for curve in curves:
        if args.bounds:
            curve['global_bounds']=certify_bounds(curve)
        print(curve['id'],curve['extrema']['min_real'][1],curve['extrema']['max_real'][1], flush=True)
    result=dict(precision_bits=ctx.prec,
                columns=['clockwise_turn_degrees','Re(w)','Im(w)','dRe/d(clockwise radians)','dIm/d(clockwise radians)'],
                curves=curves)
    if args.index is not None:
        (HERE/f'summary-{args.index}.json').write_text(json.dumps(curves[0],separators=(',',':'),ensure_ascii=False)+'\n',encoding='utf8')
    else:
        (HERE/'curves.json').write_text(json.dumps(result,separators=(',',':'),ensure_ascii=False)+'\n',encoding='utf8')

if __name__=='__main__':
    main()
