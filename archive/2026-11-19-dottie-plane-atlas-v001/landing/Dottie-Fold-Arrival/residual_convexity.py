"""Directed convexity check for one half the squared ordinary-zeta residual."""
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from flint import acb_series, arb, ctx

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"Dottie-Sixth-Passes"/"compute"))
from verify import BASE, Branch, square
from turning import enclosure


def measure():
    ctx.prec,ctx.cap=192,4
    branch=Branch(HERE.parent)
    lo,hi=BASE+F(59,4)/180,F(1,4)
    node=branch.at(lo)
    stack=[(lo,hi)]
    lower,upper=None,None
    cells=0
    while stack:
        l,r=stack.pop()
        tube=branch.centered_tube(node,branch.radius,l,r)
        if tube is not None:
            end,_,rad,center=tube
            v,a=enclosure(center,rad,l,r)
            z=acb_series([square(center,rad),1],3).zeta()
            z1=z[1]*v
            z2=2*z[2]*v**2+z[1]*a
            d2=abs(z1)**2+(z[0].conjugate()*z2).real
            if d2>1 and d2<6:
                lower=d2.lower() if lower is None else min(lower,d2.lower())
                upper=d2.upper() if upper is None else max(upper,d2.upper())
                node=end
                cells+=1
                continue
        assert r-l>F(1,2**40),(l,r)
        m=(l+r)/2
        stack.extend(((m,r),(l,m)))
    assert abs(node-branch.at(hi))+branch.radius<arb("1e-9")
    from verify import ball
    assert branch.disk_check(node,arb("1e-9"),ball(hi))[2]
    return dict(angle_degrees=[14.75,15],precision_bits=ctx.prec,accepted_cells=cells,
                source_sha256=branch.digest,observable="one half the squared modulus of ordinary zeta on w(h)",
                strict_lower_second_derivative=1,strict_upper_second_derivative=6,
                extrema_of_interval_enclosures=[lower.str(16),upper.str(16)],
                endpoint="The sixth Riemann zero has value zero, so the observable and its derivative vanish at h=15.")


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    result=measure()
    (HERE/"residual_convexity.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result)
