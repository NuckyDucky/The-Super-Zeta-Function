"""Follow the previously frozen endpoint 0.01 degree farther clockwise."""
import json
from fractions import Fraction
from flint import acb, arb, ctx
from dyadic_geometry import HERE, parsed, tangent
from arithmetic_braid import complex_record
from arithmetic_holdout_replay import centered_tube

def run():
    ctx.prec=256
    ctx.cap=3
    stored=parsed(json.loads((HERE/'dyadic_continuation.json').read_text())['terminal'])
    node=stored.mid()
    r=arb('1e-16')
    assert abs(stored-node)<r
    a=Fraction(1,4)
    b=a+Fraction(1,18000)
    queue=[(a,b,0)]
    steps=0
    minslope=arb(1000)
    while queue:
        left,right,depth=queue.pop()
        assert depth<20
        result=centered_tube(node,r,left,right)
        if result is not None:
            end,q,radius,center=result
            velocity=tangent(center,radius,left,right)
            if velocity.real>0:
                minslope=min(minslope,velocity.real.lower()/180)
                steps+=1
                node=end
                continue
        half=(left+right)/2
        queue.extend(((half,right,depth+1),(left,half,depth+1)))
    where=node+acb(arb(0,r),arb(0,r))
    assert where.real>arb(1)/2
    z=where.zeta()
    assert not z.contains(0)
    return dict(angle_degrees='4499/100',shift=str(b),segments=steps,
                minimum_rightward_velocity_per_clockwise_degree=minslope.str(20),
                reference_zero=complex_record(where),absolute_Riemann_zeta=abs(z).str(28))
if __name__=='__main__':
    data=run()
    (HERE/'dyadic_after_landing.json').write_text(json.dumps(data,indent=2)+'\n')
    print(data)
