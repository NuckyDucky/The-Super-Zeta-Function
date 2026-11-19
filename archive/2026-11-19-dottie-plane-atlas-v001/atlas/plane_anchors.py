"""Independent directed continuation of two nonzero Hurwitz levels in the atlas."""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
from flint import acb, acb_series, arb, ctx

HERE=Path(__file__).resolve().parent


def ball(x):
    return arb(x.numerator)/x.denominator


def hull(a,b):
    return acb(a.real.union(b.real),a.imag.union(b.imag))


def square(w,r):
    return w+acb(arb(0,r),arb(0,r))


def h(w,b):
    return w.zeta(b)+w.zeta(1-b)


def hb(w,b):
    return w*((w+1).zeta(1-b)-(w+1).zeta(b))


def hw(w,b):
    return h(acb_series([w,1],2),b)[1]


def newton(w,b,c,n):
    z=w.mid()
    for _ in range(n):
        z=(z-(h(z,b)-c)/hw(z,b)).mid()
    return z


def tube(node,rnode,bl,br,c):
    span=bl.union(br)
    mid=span.mid()
    half=span.rad()
    z=newton(node,mid,c,3)
    der=hw(z,mid)
    d=der.mid()
    residual=abs(h(z,mid)-c)+half*abs(hb(z,span))
    radius=max(8*rnode,(3*residual/abs(d)).upper(),(2*abs(z-node)).upper())
    if radius>arb('.3'): return None
    t=acb_series([square(z,radius),1],3)
    hww=2*h(t,span)[2]
    hwb=hb(acb_series([z,1],2),span)[1]
    k=(abs(d-der)+radius*abs(hww)+half*abs(hwb))/abs(d)
    if not (k<1 and residual/abs(d)+k*radius<radius): return None
    assert abs(z-node)+rnode<radius
    end=newton(z,br.mid(),c,4)
    if not abs(end-z)+rnode<radius: return None
    if not abs((h(end,br)-c)/d)+k*rnode<rnode: return None
    return end,k


def proof(x,y,float_x,B0):
    # Cover the exact decimal coordinates and the binary input of the grid.
    u=acb(arb(x).union(arb(float_x)),arb(y))
    c=h(u,B0)
    assert not c.contains(0)
    rnode=arb('5e-12')
    node=u.mid()
    assert abs(node-u)<rnode
    B=lambda s:(1-ball(s))*B0+ball(s)/4
    count=0
    worst=arb(0)
    queue=[(F(0),F(1))]
    while queue:
        l,r=queue.pop()
        ok=tube(node,rnode,B(l),B(r),c)
        if ok is not None:
            node,k=ok
            worst=max(worst,k.upper())
            count+=1
            continue
        assert r-l>F(1,2**32)
        mid=(l+r)/2
        queue.extend([(mid,r),(l,mid)])
    out=square(node,rnode)
    multiplier=hw(u,B0)/hw(out,arb(1)/4)
    return dict(start=[x,y],level=[c.real.str(23),c.imag.str(23)],cells=count,
                maximum_disk_contraction=worst.str(12),terminal_disk_radius=rnode.str(5),
                end=[out.real.str(22),out.imag.str(22)],length=abs(multiplier).str(22),
                derivative=[multiplier.real.str(24),multiplier.imag.str(24)])


def run():
    ctx.prec,ctx.cap=192,3
    data=json.loads((HERE/'plane_reference.json').read_bytes())
    hr=arb(data['trough']['alpha'])
    # Include both the certified trough and the rounded first input in the plot.
    B=(arb(1)/6+hr/180).union(arb(1/6+float(hr.mid())/180))
    records=[proof('.075','36.75',0.07499999999999996,B),
             proof('-.525','37.3125',-0.525,B)]
    assert arb(records[0]['length'])<arb('.287')
    assert arb(records[1]['length'])>8
    return dict(precision_bits=ctx.prec,initial_shift=B.str(25),certificates=records)


if __name__=='__main__':
    if not __debug__: raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=HERE,help="Folder for the generated certificate")
    args=parser.parse_args()
    args.output.mkdir(exist_ok=True,parents=True)
    result=run()
    (args.output/'plane_anchors.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result)
