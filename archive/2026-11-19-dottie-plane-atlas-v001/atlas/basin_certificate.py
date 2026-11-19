"""Two infinite-time destinations for one disk about w=37i. python-flint 0.9.0."""
import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
from flint import acb, acb_series, arb, ctx

HERE=Path(__file__).resolve().parent


def ball(x):
    return arb(x.numerator)/x.denominator


def square(z,r):
    return z+acb(arb(0,r),arb(0,r))


def f(z):
    q=(z*arb(2).log()).exp()
    return q*(q-1)*z.zeta()


def deriv(z):
    return f(acb_series([z,1],2))[1]


def derivative_variation(z,r):
    # Bound the derivative on the disk by integrating the second derivative
    # on the enclosing complex square from the center.
    a=f(acb_series([square(z,r),1],3))
    return r*abs(2*a[2])


def approximate(z,target):
    for _ in range(4):
        z=(z-(f(z)-target.mid())/deriv(z)).mid()
    return z


def tube(node,node_radius,left,right,ell,level):
    l,r=ball(left),ball(right)
    m,half=(l+r)/2,(r-l)/2
    target_mid=(m*ell).exp()*level
    center=approximate(node,target_mid)
    d=deriv(center)
    slope=d.mid()
    drift=half*abs(ell)*abs(level)*(l*ell.real).exp()
    residual=abs(f(center)-target_mid)+drift
    radius=max(4*node_radius,(2*abs(center-node)).upper(),(3*residual/abs(slope)).upper())
    if radius>arb('.20'): return None
    k=(abs(d-slope)+derivative_variation(center,radius))/abs(slope)
    if not(k<1 and residual/abs(slope)+k*radius<radius): return None
    assert abs(node-center)+node_radius < radius
    target_end=(r*ell).exp()*level
    end=approximate(center,target_end)
    if not(abs(end-center)+node_radius<radius and
           abs(f(end)-target_end)/abs(slope)+k*node_radius<node_radius):
        return None
    return end,k


def prove(ell,root,reach=F(4)):
    start=acb(0,37)
    input_radius=arb("1e-6")
    # Keep the initial level around its true, shared value for every point
    # in the closed disk, using an interval derivative for its variation.
    level=square(f(start),input_radius*abs(deriv(square(start,input_radius))))
    node_radius=arb("1e-4")
    node=start
    assert input_radius<node_radius and not level.contains(0) and ell.real<0
    q=[(F(0),reach)]
    accepted=0
    maximum=arb(0)
    while q:
        l,r=q.pop()
        result=tube(node,node_radius,l,r,ell,level)
        if result is not None:
            node,k=result
            maximum=max(maximum,k.upper())
            accepted+=1
            continue
        assert r-l>F(1,2**35),(l,r)
        m=(l+r)/2
        q.extend([(m,r),(l,m)])
    radius=arb(1)/64
    center=root.mid()
    d=deriv(center)
    slope=d.mid()
    k=(abs(d-slope)+derivative_variation(center,radius))/abs(slope)
    assert abs(root-center)<radius
    assert abs(node-center)+node_radius<radius
    tail_level=abs(level)*(ball(reach)*ell.real).exp()
    tail_displacement=(abs(f(center))+tail_level)/abs(slope)
    assert k<1 and tail_displacement+k*radius<radius
    # For any two points on this convex disk, the centered derivative
    # estimate also bounds inverse distances. Compare the lifted point
    # to the known exact zero to get a limit for all future t, with a rate.
    inverse_lipschitz=1/(abs(slope)*(1-k))
    rate_coefficient=abs(level)*inverse_lipschitz
    return dict(ell=[ell.real.str(30),ell.imag.str(30)],initial_disk_radius="1e-6",
                finite_cutoff=str(reach),accepted_tubes=accepted,
                maximum_finite_contraction=maximum.str(16),endpoint_disk_radius="1e-4",
                cutoff_center=[node.real.str(24),node.imag.str(24)],
                root=[root.real.str(25),root.imag.str(25)],root_disk_radius="1/64",
                uniform_tail_contraction=k.upper().str(18),
                max_tail_newton_image_radius=(tail_displacement+k*radius).upper().str(18),
                absolute_distance_coefficient=rate_coefficient.upper().str(18),
                decay_bound="abs(w(t)-root) <= coefficient * exp(t*Re(ell)), t >= 4")


def run(path):
    ctx.prec,ctx.cap=192,3
    data=json.loads(path.read_bytes())
    angles=data["lifted_log_multiplier"]
    ell=acb(arb(angles[0]),arb(angles[1]))
    principal=ell+acb(0,2*arb.pi())
    elementary=acb(0,8*arb.pi()/arb(2).log())
    rho=acb.zeta_zero(6)
    assert abs(rho-elementary)>2/arb(32)
    return dict(precision_bits=ctx.prec,input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                function="f(w)=2^w (2^w-1) zeta(w)",starting_center="37i",
                principal_k4=prove(principal,elementary),ordered_rho6=prove(ell,rho))


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input",type=Path,default=HERE/"phase_lift.json")
    parser.add_argument("--output",type=Path,default=HERE/"basin_certificate.json")
    args=parser.parse_args()
    result=run(args.input)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))
