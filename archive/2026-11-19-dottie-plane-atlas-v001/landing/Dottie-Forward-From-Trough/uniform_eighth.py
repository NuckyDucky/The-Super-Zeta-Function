"""Bound the complex quadratic-prediction error on ten full final subarcs.

Only initial packets and Hurwitz derivatives enter the bound. All variables
are measured in clockwise degrees. No Riemann endpoint lookup is required.
"""
from fractions import Fraction as F
import sys
from flint import ctx, arb
from forward import HERE, OUT, read, initial, ball, centered_tube, seal, digest
from verify import square
from turning import partials
sys.path.insert(0,str(OUT/"Dottie-Fold-Arrival"))
from fold_shapes import jets_from_partials


def bound(row):
    hf,b0,node,rad0=initial(row)
    assert hf==F(15)-F(1,8)
    pending=[(b0,F(1,4))]
    worst=arb(0)
    accepted=0
    while pending:
        l,r=pending.pop()
        proof=centered_tube(node,rad0,l,r)
        if proof:
            end,_,rad,c=proof
            bounds=partials(square(c,rad),ball(l).union(ball(r)),3)
            mid=partials(c,ball((l+r)/2),2)
            for n in (2,1):
                for j in range(n+1):
                    i=n-j
                    err=rad*abs(bounds[i+1,j])+ball((r-l)/2)*abs(bounds[i,j+1])
                    bounds[i,j]=square(mid[i,j],err.upper())
            jerk=abs(jets_from_partials(bounds)[2])
            if jerk.is_finite() and jerk<3:
                worst=max(jerk.upper(),worst)
                accepted+=1
                node=end
                continue
        if r-l<F(1,2**35):
            raise ArithmeticError(("uniform bound unresolved",row["case"],str(l),str(r)))
        m=(l+r)/2
        pending.extend(((m,r),(l,m)))
    return {"case":row["case"],"cells":accepted,"upper_abs_w3_per_degree_cubed":worst.str(14),
            "upper_quadratic_error_for_all_h_in_final_eighth":(worst/(6*512)).str(14)}


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    ctx.prec,ctx.cap=192,4
    path=OUT/"Dottie-Blind-Landing"/"predictions.json"
    rows=[bound(row) for row in read(path)["cases"] if row["cutoff"]=="1/8"]
    assert len(rows)==10 and len({r["case"] for r in rows})==10
    seal(HERE/"uniform_eighth.json",{"source_sha256":digest(path),"scope":"all real h from 14.875 through 15 on each of ten marked branches","working_bits":ctx.prec,"theorem":"|endpoint-P2(h)| <= sup |w third derivative| (15-h)^3 / 6","rows":rows})
