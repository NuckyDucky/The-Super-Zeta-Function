"""Follow marked source points inside gray pixels all the way to their square-root collisions."""
import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from pathlib import Path
from flint import acb,acb_series,arb,ctx
from gray_locus import direct,isolate
from plane_anchors import ball,hb,square,tube

HERE=Path(__file__).resolve().parent

def critical_curve(B0,entries):
    # Continue H_w=0 backwards. Force a mesh boundary at every collision
    # parameter to identify its critical point on this one analytic branch.
    border=F(1,4)
    start=isolate(.235950387044401+36.9451796757567j,ball(border),1,acb(0))[0]
    node=start.mid(); rnode=arb("1e-11")
    target={F(e["shift"]):e for e in entries}
    lower=F(str(B0.lower().fmpq()))
    stops=sorted(set(target)|{lower},reverse=True)
    count=0
    min_hb=None
    for goal in stops:
        todo=[(border,goal)]
        while todo:
            l,r=todo.pop()
            bm=ball((l+r)/2); span=ball(r).union(ball(l)); db=ball((l-r)/2)
            w=node
            for _ in range(3):
                jet=direct(w,bm)
                w=(w-jet[1]/(2*jet[2])).mid()
            v=direct(w,bm)
            pivot=(2*v[2]).mid()
            wb=hb(acb_series([w,1],2),span)[1]
            residual=abs(v[1])+db*abs(wb)
            R=max(8*rnode,(3*residual/abs(pivot)).upper(),(2*abs(node-w)).upper())
            if R<arb(".07"):
                region=square(w,R)
                q=abs(1-2*direct(region,span)[2]/pivot)
                hb_region=hb(region,span)
                if q<1 and abs(node-w)+rnode<R and q*R+residual/abs(pivot)<R and hb_region.real>0:
                    end=w
                    for _ in range(4):
                        jet=direct(end,ball(r))
                        end=(end-jet[1]/(2*jet[2])).mid()
                    if abs(end-w)+rnode<R and abs(direct(end,ball(r))[1]/pivot)+q*rnode<rnode:
                        node=end; count+=1
                        low=hb_region.real.lower()
                        min_hb=low if min_hb is None else min(min_hb,low)
                        continue
            assert l-r>F(1,2**44)
            m=(l+r)/2
            todo.extend([(m,r),(l,m)])
        border=goal
        if goal in target:
            entry=target[goal]
            other=acb(*[arb(x) for x in entry["critical_point"]])
            common=arb("1e-8")
            assert abs(node-other)+rnode<common
            pivot=(2*direct(node,ball(goal))[2]).mid()
            q=abs(1-2*direct(square(node,common),ball(goal))[2]/pivot)
            assert q<1 and abs(direct(node,ball(goal))[1]/pivot)+q*common<common
    return {"critical_tubes":count,"matched_pixel_critical_points":len(target),
            "lower_Re_Hb_along_branch":min_hb.str(15),
            "interpretation":"The selected simple critical point continues across the whole shift interval. The real part of its critical value increases strictly in b."}

def verify(entry,B0):
    b=ball(F(entry["shift"]))
    cguess=complex(*[float(arb(x).mid()) for x in entry["critical_point"]])
    crit,j=isolate(cguess,b,1,acb(0))
    K=j[0]
    wguess=complex(*[float(arb(x).mid()) for x in entry["start_preimage"]])
    source,_=isolate(wguess,B0,0,K)
    rnode=arb("3e-10")
    node=source.mid()
    assert abs(source-node)<rnode
    xp=arb(-3)/4+arb(entry["column"])/80
    yp=arb(147)/4+arb(entry["row"])/80
    assert abs(source.real-xp)<arb(1)/160 and abs(source.imag-yp)<arb(1)/160
    A=2*j[2]; B=hb(crit,b)
    coeff=(2*B/A).sqrt()
    eps=arb(1)/10**8
    stop=b-eps
    assert B0<stop
    at=lambda t:(1-ball(t))*B0+ball(t)*stop
    queue=[(F(0),F(1))]
    cells=0
    while queue:
        l,r=queue.pop()
        proof=tube(node,rnode,at(l),at(r),K)
        if proof:
            node=proof[0]
            cells+=1
            continue
        assert r-l>F(1,2**55)
        mid=(l+r)/2
        queue.extend([(mid,r),(l,mid)])
    # On |z +/- C sqrt(t)| = eta |C| sqrt(t), A z²/2 - B t
    # dominates the cubic, mixed and shift-quadratic Taylor remainders.
    eta=arb(1)/4
    bound=(1+eta)*abs(coeff)
    wbox=square(crit,bound*eps.sqrt())
    span=b.union(stop)
    www=abs(6*direct(wbox,b,4)[3])
    wb=abs(hb(acb_series([wbox,1],2),span)[1])
    bb=abs(wbox*(wbox+1)*((wbox+2).zeta(span)+(wbox+2).zeta(1-span)))
    main=abs(B)*eta*(2-eta)
    error=(www*bound**3/6+wb*bound)*eps.sqrt()+bb*eps/2
    assert main>error
    hit=[s for s in (1,-1) if abs(node-crit-s*coeff*eps.sqrt())+rnode<eta*abs(coeff)*eps.sqrt()]
    assert len(hit)==1
    return {"row":entry["row"],"col":entry["column"],"collision_h":(180*(b-arb(1)/6)).str(18),
            "source":[source.real.str(17),source.imag.str(17)],"critical_point":[crit.real.str(19),crit.imag.str(19)],
            "initial_disk_radius":rnode.str(6),"certified_tubes":cells,"sqrt_t_sheet_sign":hit[0],
            "t_is_shift_distance":"b_collision-b","sqrt_coefficient":[coeff.real.str(17),coeff.imag.str(17)],
            "rouche_main_lower":main.lower().str(12),"rouche_error_upper":error.upper().str(12)}

def worker(args):
    entry,h_text=args
    ctx.prec,ctx.cap=192,4
    h=arb(h_text)
    B0=(arb(1)/6+h/180).union(arb(1/6+float(h.mid())/180))
    return verify(entry,B0)

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--locus",type=Path,default=HERE/"gray_locus.json")
    p.add_argument("--out",type=Path,default=HERE/"gray_collision.json")
    args=p.parse_args()
    ctx.prec,ctx.cap=192,4
    h_text=json.loads((HERE/"plane_reference.json").read_bytes())["trough"]["alpha"]
    h=arb(h_text)
    B0=(arb(1)/6+h/180).union(arb(1/6+float(h.mid())/180))
    rows=json.loads(args.locus.read_bytes())["pixel_checks"]
    curve=critical_curve(B0,rows)
    with ProcessPoolExecutor(max_workers=3) as pool:
        cases=list(pool.map(worker,[(entry,h_text) for entry in rows]))
    data={"precision_bits":ctx.prec,"critical_curve":curve,"illustrated_pixels":cases,
          "meaning":"Within each source square a point on a specified Hurwitz level travels through simple roots up to the moving critical point, where a pair of roots coalesces quadratically."}
    args.out.write_bytes((json.dumps(data,indent=2)+"\n").encode())
    print(json.dumps(data,indent=2))
