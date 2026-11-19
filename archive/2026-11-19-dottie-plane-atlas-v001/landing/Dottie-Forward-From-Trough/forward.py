"""Run in three separate processes: predict, certify, score. python-flint 0.9.0."""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
OUT = HERE.parent
sys.path[:0] = [str(OUT/"Dottie-Sixth-Passes"/"compute"),str(OUT/"Dottie-Off-Axis-Return")]
from verify import jets
from arithmetic_braid import ball, shrink_root
from arithmetic_reference import disk_check
from arithmetic_holdout_replay import centered_tube


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def seal(path, record):
    data=(json.dumps(record,indent=2,ensure_ascii=False)+"\n").encode()
    with path.open("xb") as stream:
        stream.write(data)
    print(path.name, digest(path),flush=True)


def unpack(z): return acb(arb(z["real"]),arb(z["imag"]))
def pack(z): return {"real":z.real.str(43),"imag":z.imag.str(43)}


def initial(row):
    h=arb(row["h"])
    hf=F(str(h.mid().fmpq()))
    point=unpack(row["z"])
    b=F(1,6)+hf/180
    center=shrink_root(point.mid(),ball(b),3)
    r=arb("1e-30")
    common=arb("1e-9")
    assert abs(point-center)<common
    span=(arb(1)/6+h/180).union(ball(b))
    assert disk_check(center,common,span)[2] and disk_check(center,r,ball(b))[2]
    return hf,b,center,r


def predict(row,counts):
    hf,_,start,_=initial(row)
    answers={}
    for count in counts:
        step=(F(15)-hf)/count
        z=start
        for i in range(count):
            b=F(1,6)+(hf+i*step)/180
            v,a=jets(z,ball(b))
            z=(z+ball(step)*v+ball(step)**2*a/2).mid()
            if not z.is_finite(): raise ArithmeticError(("fixed-step divergence",row["case"],count,i))
        answers[str(count)]=pack(z)
    return {"case":row["case"],"predicted":answers}


def certify(row):
    _,b,node,r=initial(row)
    stack=[(b,F(1,4))]
    tests=cells=0
    while stack:
        left,right=stack.pop()
        tests+=1
        if tests>4096: raise ArithmeticError("4096 interval budget exceeded")
        proof=centered_tube(node,r,left,right)
        if proof:
            node=proof[0]
            cells+=1
            continue
        mid=(left+right)/2
        stack.extend(((mid,right),(left,mid)))
    assert disk_check(node,r,ball(F(1,4)))[2]
    return {"case":row["case"],"center":pack(node),"disk_radius":"1e-30","tested":tests,"accepted":cells}


def main(mode, packets):
    ctx.prec,ctx.cap=224,4
    model=HERE/"predicted.json"
    cert=HERE/"certified.json"
    defs=HERE/"protocol.json"
    rows=[{k:v[k] for k in ("case","h","z")} for v in read(packets)["cases"] if v["cutoff"]=="trough"]
    assert len(rows)==10 and len({r["case"] for r in rows})==10
    key={"protocol_sha256":digest(defs),"packet_sha256":digest(packets)}
    counts=read(defs)["fixed_steps"]
    if mode=="predict":
        seal(model,{**key,"predictions":[predict(r,counts) for r in rows]})
        return
    frozen=read(model)
    assert all(frozen[k]==v for k,v in key.items())
    if mode=="certify":
        seal(cert,{**key,"predictions_sha256":digest(model),"endpoints":[certify(r) for r in rows]})
        return
    proven=read(cert)
    assert proven["predictions_sha256"]==digest(model) and all(proven[k]==v for k,v in key.items())
    scores=[]
    zeros=[acb.zeta_zero(k) for k in range(1,11)]
    for row,entry in zip(frozen["predictions"],proven["endpoints"],strict=True):
        assert row["case"]==entry["case"]
        c,r=unpack(entry["center"]),arb(entry["disk_radius"])
        match=[k for k,z in enumerate(zeros,1) if abs(c-z)<r]
        assert len(match)==1
        # H at b=1/4 is a nonvanishing factor times Riemann zeta on these
        # disks. Each encloses a unique H zero, identifying the enclosed point.
        err={k:(abs(unpack(z)-c)+arb(0,r)).str(16) for k,z in row["predicted"].items()}
        scores.append({"case":row["case"],"verified_ordinal":match[0],"errors":err})
    seal(HERE/"scored.json",{**key,"certificate_sha256":digest(cert),"scores":scores})


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode",choices=["predict","certify","score"])
    p.add_argument("--packets",type=Path,default=OUT/"Dottie-Blind-Landing"/"predictions.json")
    a=p.parse_args()
    main(a.mode,a.packets)
