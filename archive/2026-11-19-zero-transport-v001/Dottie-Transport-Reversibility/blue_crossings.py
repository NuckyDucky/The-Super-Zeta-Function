"""Count every critical-line intersection on the sealed sweep from rho_4."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
from flint import arb, acb, ctx

here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/'Dottie-Second-Zero'))
from dyadic_geometry import parsed, tangent
from arithmetic_braid import ball, complex_record
from arithmetic_holdout_replay import centered_tube

def run():
    pts=json.loads((here.parent/'Dottie-Forward-Iteration'/'sweep_2.json').read_bytes())['checkpoints']
    eps=arb('1e-16')
    half=arb(1)/2
    small_square=acb(arb(0,eps),arb(0,eps))
    def sign(h):
        assert not h.contains(0)
        return 1 if h>0 else -1
    # Adaptive validated continuation when narrowing a crossing bracket.
    def advance(node,a,b):
        tube=centered_tube(node,eps,a,b)
        if tube is not None: return tube[0]
        m=(a+b)/2
        return advance(advance(node,a,m),m,b)
    events=[]
    segments=0
    max_real=None
    for j in range(len(pts)-1):
        a0,b0=[F(p['shift']) for p in pts[j:j+2]]
        z0,z1=[parsed(p['zero']) for p in pts[j:j+2]]
        node=z0.mid()
        assert abs(z0-node)<eps
        right_sign=sign(z1.real-half)
        left_sign=right_sign if j==0 else sign(z0.real-half)
        crossing=right_sign!=left_sign
        queue=[(a0,b0,0)]
        while queue:
            a,b,d=queue.pop()
            tube=centered_tube(node,eps,a,b)
            if tube is not None:
                end,q,r,c=tube
                valid=(not crossing and left_sign*(c.real-half)>r)
                if not valid:
                    velocity=tangent(c,r,a,b)
                    if crossing:
                        valid=right_sign*velocity.real>0
                    else:
                        from_left=(left_sign*velocity.real>0 and
                                   (a==F(1,6) or left_sign*(node.real-half)>eps))
                        from_right=(left_sign*velocity.real<0 and left_sign*(end.real-half)>eps)
                        valid=from_left or from_right
                if valid:
                    segments+=1
                    node=end
                    continue
            assert d<35,(j,a,b)
            m=(a+b)/2
            queue.extend(((m,b,d+1),(a,m,d+1)))
        assert abs(node-z1)<2*eps
        if crossing:
            a,b=a0,b0
            n=z0.mid()
            for _ in range(27):
                m=(a+b)/2
                mid=advance(n,a,m)
                assert abs(mid.real-half)>eps
                if sign(mid.real-half)==right_sign: b=m
                else: a=m;n=mid
            tube=centered_tube(n,eps,a,b)
            assert tube is not None
            _,_,r,c=tube
            w=acb(half,c.imag+arb(0,r))
            theta=ball(180*(F(1,2)-b)).union(ball(180*(F(1,2)-a)))
            magnitude=abs(w.zeta())
            assert magnitude>0
            events.append(dict(cell=j,angle=theta.str(22),degrees_from_start=(60-theta).str(22),
                               height=w.imag.str(22),abs_riemann_zeta=magnitude.str(22),
                               direction='right to left' if right_sign<0 else 'left to right'))
    furthest_sample=parsed(pts[217]['zero'])
    assert furthest_sample.real>arb('0.50053')
    return dict(sweep=2,precision_bits=ctx.prec,segments=segments,includes_seed=False,
                interior_crossings=events,upper_loop_sample=complex_record(furthest_sample),
                sample_angle=str(180*(F(1,2)-F(pts[217]['shift']))))

if __name__=='__main__':
    ctx.prec,ctx.cap=256,3
    result=run()
    (here/'blue-crossings.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result)
