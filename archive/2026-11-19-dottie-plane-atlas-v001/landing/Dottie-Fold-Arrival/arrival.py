"""Arrival jets for the frozen Hurwitz tracks. Run with Python 3.12 and python-flint 0.9.0."""
import json
import sys
from fractions import Fraction as F
from pathlib import Path

from flint import acb, acb_series, arb, ctx, dirichlet_char

HERE = Path(__file__).resolve().parent
OUT = HERE.parent
sys.path[:0] = [str(OUT/"Dottie-Turn-Geometry"/"ten"), str(OUT/"Dottie-Sixth-Passes"/"compute")]
from geometry import FILES, get_points
from verify import Branch, ball, jets, square


def numerator(z):
    # Positive residue classes mod 4, weighted by the real primitive character.
    return z*acb(4)**(z+1)*(z+1).dirichlet_l(dirichlet_char(4,3))/180


def factor(z):
    p = acb(2)**z
    return p*(p-1)


def fmt(z):
    return z.str(24)


def sample(rank):
    nodes=get_points(rank)
    p=acb.zeta_zero(rank) if rank else acb(0,8*arb.pi()/arb(2).log())
    assert abs(p-nodes[-1][1])<arb("1e-9")
    v,a=jets(p,arb(1)/4)
    variable=acb_series([p,1],3)
    ordinary=variable.zeta()
    dyadic=(acb(2).log()*variable).exp()
    kjet=dyadic*(dyadic-1)
    pj=variable*((variable+1)*acb(4).log()).exp()*(variable+1).dirichlet_l(dirichlet_char(4,3))
    hbb=p*(p+1)*factor(p+2)*(p+2).zeta()
    hw=numerator(p)/v
    hww=(2*pj[1]*v/180-hbb/180**2-hw*a)/v**2
    if rank:
        reconstructed=numerator(p)/(factor(p)*v)
        direct=ordinary[1]
        next_jet=(hww-2*kjet[1]*reconstructed)/factor(p)
        check_next=2*ordinary[2]
        observable="zeta_prime"
    else:
        reconstructed=numerator(p)/(arb(2).log()*v)
        direct=p.zeta()
        next_jet=(hww-2*kjet[2]*reconstructed)/(2*kjet[1])
        check_next=ordinary[1]
        observable="zeta"
    assert abs(reconstructed-direct)<arb("1e-54") and reconstructed.overlaps(direct)
    assert abs(next_jet-check_next)<arb("1e-54") and next_jet.overlaps(check_next)
    assert abs(v)>0
    rho6_as_seed=None
    if rank==8:
        start=acb.zeta_zero(6)
        assert abs(start-nodes[0][1]) < arb("1e-9")
        initial_v, initial_a=jets(start,arb(1)/6)
        rho6_as_seed={"v":fmt(initial_v), "a":fmt(initial_a), "speed":fmt(abs(initial_v)),
                      "speed_change":fmt((initial_v.conjugate()*initial_a).real/abs(initial_v))}
    return {"start":FILES[rank][1], "end_rank":rank or None, "end":fmt(p),
            "velocity":fmt(v),"acceleration":fmt(a),"speed":fmt(abs(v)),
            "speed_change":fmt((v.conjugate()*a).real/abs(v)),
            "observable":observable,"recovered":fmt(reconstructed),"direct":fmt(direct),
            "next_derivative_from_acceleration":fmt(next_jet), "direct_next_derivative":fmt(check_next),
            "direct_overlap":True, "as_reset":rho6_as_seed}


def acceleration_bound(branch, left, right):
    tube=branch.centered_tube(branch.at(left),branch.radius,left,right)
    if tube is not None:
        _,_,r,c=tube
        _,acc=jets(square(c,r),ball(left).union(ball(right)))
        bound=abs(acc)
        if bound.is_finite() and bound<arb(2):
            return bound.upper()
    assert right-left>F(1,2**60)
    mid=(left+right)/2
    return max(acceleration_bound(branch,left,mid),acceleration_bound(branch,mid,right))


def inward(branch,eps):
    target=F(1,4)
    b1,b2=target-eps/180,target-2*eps/180
    one=square(branch.at(b1),branch.radius)
    two=square(branch.at(b2),branch.radius)
    e=ball(eps)
    max_acc=acceleration_bound(branch,b2,target)
    z=2*one-two
    vel=(one-two)/e
    # Extrapolate from the two interior points. M bounds the complex acceleration.
    zbox=square(z,max_acc*e**2)
    vbox=square(vel,3*max_acc*e/2)
    estimate=numerator(z)/(factor(z)*vel)
    certified=numerator(zbox)/(factor(zbox)*vbox)
    exact_root=acb.zeta_zero(6)
    exact_derivative=acb_series([exact_root,1],2).zeta()[1]
    assert zbox.contains(exact_root) and certified.contains(exact_derivative)
    assert not vbox.contains(0) and not factor(zbox).contains(0)
    return {"interior_distance_degrees":str(eps),"acceleration_uniform_upper":fmt(max_acc),
            "estimated_root":fmt(z),"estimated_zeta_prime":fmt(estimate),
            "zeta_prime_enclosure":fmt(certified),"root_error_upper":fmt(max_acc*e**2),
            "speed_vector_error_upper":fmt(3*max_acc*e/2),
            "absolute_observed_difference":fmt(abs(estimate-exact_derivative)),
            "endpoint_overlap":True}


def spectral_series(branch,clockwise):
    # Validate the exact all-order formula against directed ordinary zeta.
    b=F(1,6)+clockwise/180
    z=square(branch.at(b),branch.radius)
    shift=ball(b-F(1,4))
    x=4*abs(shift)
    assert z.real>0 and x<1 and not factor(z).contains(0)
    odd_sum=(1-arb(2)**(-z.real-1))*(z.real+1).zeta()
    common=odd_sum/abs(1-acb(2)**(-z))
    direct=z.zeta()
    aggregate=acb(0)
    weight=acb(1)
    abs_binomial=arb(1)
    rows=[]
    for j in range(1,25):
        weight=weight*(z+j-1)*shift/j
        abs_binomial=abs_binomial*(abs(z)+j-1)/j
        zw=z+j
        if j%2:
            aggregate+=weight*(acb(4)**zw)*zw.dirichlet_l(dirichlet_char(4,3))
        else:
            aggregate-=weight*factor(zw)*zw.zeta()
        if j in [4,8,12,16,24]:
            first=abs_binomial*(abs(z)+j)/(j+1)*x**(j+1)
            ratio=x*max(arb(1),(abs(z)+j+1)/(j+2))
            assert ratio<1
            err=common*first/(1-ratio)
            approx=aggregate/factor(z)
            assert square(approx,err).overlaps(direct)
            rows.append({"terms":j,"tail_modulus_upper":fmt(err.upper()),
                         "sum":fmt(approx),"observed_difference":fmt(abs(approx-direct))})
    return {"clockwise_degrees":str(clockwise),"root":fmt(z),"ordinary_zeta":fmt(direct),"bounds":rows}


def run():
    ctx.prec,ctx.cap=256,3
    cases=[sample(rank) for rank in [*range(1,11),0]]
    br=Branch(OUT)
    secants=[inward(br,F(1,10**k)) for k in [2,4,6,8]]
    expansion=[spectral_series(br,h) for h in (F(29,2), F(149,10))]
    chart=json.loads((OUT/"Dottie-Sixth-Single-Term"/"contraction-sweep.json").read_bytes())
    return {"working_precision_bits":ctx.prec,"independent_library":"FLINT Hurwitz jets versus Dirichlet L and direct Riemann Taylor jet",
            "coordinate":"h in clockwise degrees from 60, b=1/6+h/180",
            "sixth_arrival_interior_secants":secants, "cases":cases,
            "sixth_zero_branch_inside_all_orders":expansion,
            "right_flank_archive":{"source":"../Dottie-Sixth-Single-Term/contraction-sweep.json",
                "speed_along_chart":"distinct from orbit attraction",
                "initial_abs_multiplier":chart["initial_abs_mu"],"arrival_abs_multiplier":chart["terminal_abs_mu"]}}


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    record=run()
    HERE.joinpath("arrival.json").write_text(json.dumps(record,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
