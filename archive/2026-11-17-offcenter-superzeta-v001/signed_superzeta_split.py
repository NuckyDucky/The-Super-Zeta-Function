"""Use the signed square of the separation to test for a reflected off-line pair.

Let H(z)=xi(1/2+iz), equivalently the completed superzeta difference. It is real
on the real axis. Write H(h+i*sqrt(q))=U+i*sqrt(q)*V by separating the even
and odd Taylor terms at h. At real q, U,V are real; this notation for q<0
means the analytic continuation of BOTH terms, using the two signs of sqrt.
For q>0, U=V=0 specifies the same-height pair with beta=1/2+-sqrt(q).
For q<0, U=V=0 specifies the two axial heights h+-sqrt(-q).
At q=0 we obtain H(h)=H'(h)=0. A simple line zero is filtered out.

For any nonvanishing real-on-real analytic change of normalization these
simultaneous zero conditions are identical. Evaluate them here for the local
complex predictor in offcenter_superzeta, then use frozen rational brackets
from its separately certified contour counts. The new pair test uses the
first prescribed window containing adjacent predicted real roots.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from offcenter_superzeta import acb, arb, ctx, geometry, phase_polynomial, save


def symmetric_horner(coeff,h,q):
    # Multiply U+i*sqrt(q)*V by 2*(h+i*sqrt(q)), the forecast variable.
    U,V=0.,0.
    for c in reversed(coeff):
        U,V=2*h*U-2*q*V+c,2*U+2*h*V
    return U,V


def candidates(roots):
    on_line=sorted(r["height_offset"] for r in roots if r["beta"]==.5)
    for a,b in zip(on_line,on_line[1:]):
        yield (a+b)/2,-((b-a)/2)**2
    # One representative of each off-line mirror pair of the real polynomial.
    for root in roots:
        if root["beta"]>.5:
            yield root["height_offset"],(root["beta"]-.5)**2


def predict(path):
    raw=path.read_bytes()
    results=[]
    for level in json.loads(raw)["levels"]:
        pairs=list(candidates(level["predicted_roots"]))
        if not pairs:
            continue
        _,_,coeff=phase_polynomial(level["level"])
        for h,q in pairs:
            U,V=symmetric_horner(coeff,h,q)
            assert abs(U)<1e-7 and abs(V)<1e-7
            results.append({"level":level["level"],"height_offset":h,"signed_square":q,
                            "model_even_residual":U,"model_divided_odd_residual":V})
    return {"forecast_sha256":hashlib.sha256(raw).hexdigest(),"pairs":results}


def compare(pair_path,cert_path):
    pairs=json.loads(pair_path.read_text(encoding="utf-8"))
    cert=json.loads(cert_path.read_text(encoding="utf-8"))
    assert pairs["forecast_sha256"]==cert["prediction_sha256"]
    for row in cert["results"]:
        H,eps=geometry(row["level"])
        t=arb(1)/4
        a,b=acb(H,t),acb(H,-t)
        fa,fb=a.cos()**2-(a/eps)**2,b.cos()**2-(b/eps)**2
        even,odd=(fa+fb)/2,(fa-fb)/acb(0,2*t)
        assert even.contains(0) and odd.contains(0) and row["cosine_right"]["count"]==1
        print("Cosine positive control: level",row["level"],"signed square +1/16.")
    for pair in pairs["pairs"]:
        row=next(r for r in cert["results"] if r["level"]==pair["level"])
        if pair["signed_square"]>0:
            box=next(b for b in row["off_axis_forecast_tests"]
                     if b["predicted_root"]["height_offset"]==pair["height_offset"]
                     and (b["predicted_root"]["beta"]-.5)**2==pair["signed_square"])
            print("Positive split prediction, certified off-center count",box["count"],
                  "real bounds",box["real"],"height-offset bounds",box["offset"])
            continue
        brackets=[tuple(map(Fraction,b)) for b in row["line_brackets_offsets"]]
        assert row["off_line_upper_bound"]==0
        # Match the pair to adjacent disjoint brackets using its frozen midpoint.
        h=Fraction.from_float(pair["height_offset"])
        matches=[(l,r) for l,r in zip(brackets,brackets[1:]) if l[1]<h<r[0]]
        assert len(matches)==1
        l,r=matches[0]
        lo=-((r[1]-l[0])/2)**2
        hi=-((r[0]-l[1])/2)**2
        assert lo<=Fraction.from_float(pair["signed_square"])<=hi<0
        print("Certified q interval, exact:",lo,hi)
        print("Endpoints, rounded:",float(lo),float(hi))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode",choices=["predict","check"])
    p.add_argument("input",type=Path)
    p.add_argument("second",type=Path)
    a=p.parse_args()
    ctx.prec=192
    if a.mode=="predict":
        result=predict(a.input)
        save(a.second,result)
        print(json.dumps(result,indent=2))
    else:
        compare(a.input,a.second)
