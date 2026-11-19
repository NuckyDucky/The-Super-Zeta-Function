"""Check rising height and isolate all intersections with Re(w)=1/2."""
from fractions import Fraction
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'Dottie-Second-Zero'))
from dyadic_geometry import parsed, tangent
from arithmetic_braid import ball, complex_record
from arithmetic_holdout_replay import centered_tube


def run():
    ctx.prec, ctx.cap = 256, 3
    path=json.loads((HERE/'sweep_1.json').read_bytes())['checkpoints']
    r=arb('1e-15')
    half=arb(1)/2
    start,finish=Fraction(1,6),Fraction(1,4)
    low,high=158,163
    assert parsed(path[low]['zero']).real<half and parsed(path[high]['zero']).real>half
    slopes=[]
    def certified_side(w,a,b,node,end,rad,vel,sign):
        if sign*(w.real-half)>rad:
            return True
        if sign*vel.real>0 and (a==start or sign*(node.real-half)>r):
            return True
        return bool(sign*vel.real<0 and (b==finish or sign*(end.real-half)>r))
    for j in range(256):
        left,right=[Fraction(p['shift']) for p in path[j:j+2]]
        point=parsed(path[j]['zero'])
        node=point.mid()
        assert abs(point-node)<r
        pending=[(left,right,0)]
        while pending:
            a,b,d=pending.pop()
            tube=centered_tube(node,r,a,b)
            if tube:
                end,_,rad,w=tube
                vel=tangent(w,rad,a,b)
                side=-1 if j<low else 1
                if vel.is_finite() and vel.imag>0 and (
                        (low<=j<high and vel.real>0) or
                        ((j<low or j>=high) and certified_side(w,a,b,node,end,rad,vel,side))):
                    slopes.append(vel.imag.lower())
                    node=end
                    continue
            assert d<32
            m=(a+b)/2
            pending.extend(((m,b,d+1),(a,m,d+1)))
        assert abs(node-parsed(path[j+1]['zero']))<2*r
    # Detect the bracket on the certified strictly increasing real portion.
    index=next(j for j in range(low,high) if parsed(path[j+1]['zero']).real>half)
    a,b=(Fraction(p['shift']) for p in path[index:index+2])
    node=parsed(path[index]['zero']).mid()
    for _ in range(25):
        m=(a+b)/2
        tube=centered_tube(node,r,a,m)
        assert tube
        end=tube[0]
        assert abs(end.real-half)>r
        if end.real>half: b=m
        else: a=m;node=end
    _,_,rad,w=centered_tube(node,r,a,b)
    line=acb(half,w.imag+arb(0,rad))
    magnitude=abs(line.zeta())
    assert magnitude>0
    return dict(certified_intervals=len(slopes),height_strictly_increasing=True,
                minimum_lower_bound_for_dt_db=min(slopes).str(12),
                total_interior_critical_line_crossings=1,
                crossing_theta_clockwise_native_degrees=ball((Fraction(1,2)-b)*180).union(ball((Fraction(1,2)-a)*180)).str(20),
                crossing_w=complex_record(line),absolute_riemann_zeta=magnitude.str(20))

if __name__=='__main__':
    result=run()
    (HERE/'geometry.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result)
