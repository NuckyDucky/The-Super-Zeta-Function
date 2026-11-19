"""Identify the two zero sheets at the simple critical point on a straight value ray."""
import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
from flint import acb, acb_series, arb, ctx
from basin_certificate import approximate, ball, deriv, derivative_variation, f, square

HERE=Path(__file__).resolve().parent


def lift(root,fc,qend):
    # Inverse disks for f(w)=q*f(wc), keeping the *same* critical value at all q.
    node=root.mid()
    rnode=arb('1e-13')
    assert abs(root-node)<rnode
    queue=[(F(0),qend)]
    accepted=0
    worst=arb(0)
    while queue:
        l,r=queue.pop()
        m=ball((l+r)/2)
        center=approximate(node,m*fc)
        der=deriv(center)
        D=der.mid()
        residual=abs(f(center)-m*fc)+ball((r-l)/2)*abs(fc)
        R=max(4*rnode,(3*residual/abs(D)).upper(),(2*abs(center-node)).upper())
        if R<arb('.2'):
            k=(abs(der-D)+derivative_variation(center,R))/abs(D)
            if k<1 and residual/abs(D)+k*R<R:
                assert abs(node-center)+rnode<R
                goal=ball(r)*fc
                end=approximate(center,goal)
                if abs(center-end)+rnode<R and abs(f(end)-goal)/abs(D)+k*rnode<rnode:
                    node=end
                    worst=max(worst,k.upper())
                    accepted+=1
                    continue
        assert r-l>F(1,2**45),(l,r)
        m=(l+r)/2
        queue.extend([(m,r),(l,m)])
    return node,rnode,dict(accepted_tubes=accepted,maximum_newton_contraction=worst.str(13),
                           end=[node.real.str(21),node.imag.str(21)],node_radius=rnode.str(7))


def verify(source):
    ctx.prec,ctx.cap=192,4
    data=json.loads(source.read_bytes())
    box=acb(*map(arb,data['critical_w']))
    wc=box.mid()
    # Independently re-isolate the critical point, using only the printed
    # seed of the earlier receipt. Its small disk is inside the local disk.
    for _ in range(3):
        jet=f(acb_series([wc,1],3))
        wc=(wc-jet[1]/(2*jet[2])).mid()
    cr=arb('1e-28')
    crit=square(wc,cr)
    j=f(acb_series([wc,1],3))
    mixed=f(acb_series([crit,1],3))
    d=(2*j[2]).mid()
    k=abs(1-2*mixed[2]/d)
    assert k<1 and abs(j[1]/d)+k*cr<cr
    # Both printed enclosures identify the same point. This larger disk
    # contains the entire archived enclosure and our tighter disk, and
    # can contain only one zero of f'.
    common=arb('1e-18')
    cover=f(acb_series([square(wc,common),1],3))
    ck=abs(1-2*cover[2]/d)
    assert abs(wc-box)<common and cr<common and ck<1 and abs(j[1]/d)+ck*common<common
    fc=mixed[0]
    d2=2*mixed[2]
    qend=F(999999,1000000)
    roots=(acb(0,8*arb.pi()/arb(2).log()),acb.zeta_zero(6))
    a,ra,p=lift(roots[0],fc,qend)
    b,rb,q=lift(roots[1],fc,qend)
    assert abs(a-b)>ra+rb
    # These contours are centered on the exact critical point; the outer
    # square encloses every radius-R disk with the available center bounds.
    R=arb(1)/256
    assert abs(a-crit)+ra<R and abs(b-crit)+rb<R
    t=f(acb_series([square(crit,R),1],4))
    M=abs(6*t[3]).upper()
    quadratic=(abs(d2)*R**2/2).lower()
    remainder=(M*R**3/6+ball(1-qend)*abs(fc)).upper()
    assert remainder<quadratic
    # The derivative has exactly one zero here, namely wc. The two
    # distinct roots cannot collide for q<1 or leave the disk boundary.
    dmain=(abs(d2)*R).lower()
    drem=(M*R**2/2).upper()
    assert drem<dmain
    coefficient=((-2*fc/d2).sqrt())
    # Relative disks about ±coefficient*s, s=sqrt(1-q), separate both
    # sheets all the way to the fold. Divide the boundary estimates by
    # s^2 before letting s decrease, to keep a strict uniform comparison.
    smax=ball(1-qend).sqrt()
    eta=arb(1)/4
    assert (1+eta)*abs(coefficient)*smax<R
    sign_main=(abs(fc)*eta*(2-eta)).lower()
    sign_err=(M*(1+eta)**3*abs(coefficient)**3*smax/6).upper()
    assert sign_err<sign_main
    assert abs(a-crit+coefficient*smax)+ra<eta*abs(coefficient)*smax
    assert abs(b-crit-coefficient*smax)+rb<eta*abs(coefficient)*smax
    return dict(precision_bits=ctx.prec,input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            family="f(w)=q f(w_c), 0 <= q <= 1",q_cutoff=str(qend),
            root_sources=["8 pi i/log(2)","Riemann zero 6"],elementary=p,riemann=q,
            local_radius="1/256",third_derivative_upper=M.str(16),
            quadratic_boundary_lower=quadratic.str(16),remainder_plus_target_upper=remainder.str(16),
            derivative_linear_boundary_lower=dmain.str(16),derivative_remainder_upper=drem.str(16),
            sqrt_coefficient=[coefficient.real.str(14),coefficient.imag.str(14)],
            square_root_signs={"elementary_k4":-1,"riemann_6":1},
            relative_separating_disk_radius="1/4",signed_sheet_quadratic_lower=sign_main.str(16),
            signed_sheet_remainder_upper=sign_err.str(16),
            conclusion="Both continued sheets approach the same order-two branch point as q increases to one.")


if __name__=='__main__':
    if not __debug__: raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input",type=Path,default=HERE/"critical_loop.json")
    parser.add_argument("--output",type=Path,default=HERE/"critical_branches.json")
    args=parser.parse_args()
    result=verify(args.input)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))
