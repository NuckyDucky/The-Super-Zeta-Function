"""Evaluate the precommitted two-seed experiment in four separately sealed stages."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
from flint import acb, acb_series, arb, ctx

HERE=Path(__file__).resolve().parent
PROTOCOL_HASH="8ab949c14e7edb66d59dbe91da6d3bb8a252ec7857b45a9129986e0ec9b7c7cb"
START=F(0)
PROBE=F(1,4)
CUTOFF=F(119,8)
END=F(15)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def seal(path,data):
    payload=(json.dumps(data,indent=2,allow_nan=False)+"\n").encode()
    if path.exists():
        if path.read_bytes()!=payload:
            raise RuntimeError("Refusing to replace an existing seal: "+str(path))
    else:
        with path.open("xb") as handle:
            handle.write(payload)
    print(f"{path.name} {sha(path)}",flush=True)

def pack(z):
    return {"re":z.real.str(33),"im":z.imag.str(33)}

def unpack(z):
    return acb(arb(z["re"]),arb(z["im"]))

def exact_center(z):
    return [str(z.real.mid().fmpq()),str(z.imag.mid().fmpq())]

def from_center(z):
    return acb(ball(F(z[0])),ball(F(z[1])))

def ball(f):
    return arb(f.numerator)/f.denominator

def square(z,r):
    return z+acb(arb(0,r),arb(0,r))

def parameter(h):
    return F(1,6)+h/180

def sign(x):
    if x>0: return "positive"
    if x<0: return "negative"
    return "unresolved"

def jets(z,h):
    b=ball(parameter(h))
    w=acb_series([z,1],3)
    H=w.zeta(b)+w.zeta(1-b)
    Hb=-w*((w+1).zeta(b)-(w+1).zeta(1-b))
    Hbb=z*(z+1)*((z+2).zeta(b)+(z+2).zeta(1-b))
    v=-Hb[0]/H[1]
    a=-(Hbb+2*Hb[1]*v+2*H[2]*v*v)/H[1]
    return v/180,a/180**2

class Exhausted(Exception):
    pass

def advance(row,node,left,right,p,radius,centered_tube):
    n=int((right-left)*8)
    if F(n,8)<right-left: n+=1
    for j in range(n):
        l=left+(right-left)*j/n
        r=left+(right-left)*(j+1)/n
        remaining=[(l,r,0)]
        while remaining:
            h0,h1,depth=remaining.pop()
            assert FractionLast(row)==h0
            if row["tube_attempts"]>=p["max_tube_attempts_per_seed_total"]:
                raise Exhausted("tube-attempt budget")
            row["tube_attempts"]+=1
            row["max_depth"]=max(row["max_depth"],depth)
            try:
                proof=centered_tube(node,radius,parameter(h0),parameter(h1))
            except (ArithmeticError,ValueError,AssertionError):
                proof=None
            if proof is None:
                if depth>=p["max_bisection_depth_per_base_cell"]:
                    raise Exhausted("depth budget")
                m=(h0+h1)/2
                remaining.extend(((m,h1,depth+1),(h0,m,depth+1)))
                continue
            node=proof[0]
            row["accepted_tubes"]+=1
            row["last_certified_h"]=str(h1)
            row["last_center"]=exact_center(node)
    return node

def FractionLast(row):
    return F(row["last_certified_h"])

def launch(k,radius,disk_check):
    anchor=acb(0,2*k*arb.pi()/arb(3).log())
    node=anchor.mid()
    row={"k":k,"last_certified_h":"0","last_center":exact_center(node),"tube_attempts":0,"accepted_tubes":0,"max_depth":0}
    if not (abs(anchor-node)<radius and disk_check(node,radius,ball(parameter(START)))[2]):
        return dict(row,status="unresolved",reason="initial isolating disk")
    v,a=jets(anchor,START)
    return dict(row,status="launched",start=pack(anchor),initial_velocity=pack(v),
                predicted_horizontal_side=sign(v.real))

def forecast(previous,p,radius,tube):
    row=previous.copy()
    if row["status"]!="launched": return row
    try:
        node=advance(row,from_center(row["last_center"]),START,PROBE,p,radius,tube)
        probe=square(node,radius)
        row.update(probe=pack(probe),measured_horizontal_side=sign(probe.real))
        node=advance(row,node,PROBE,CUTOFF,p,radius,tube)
    except Exhausted as exc:
        return dict(row,status="unresolved",reason=str(exc))
    z=square(node,radius)
    v,a=jets(z,CUTOFF)
    d=ball(END-CUTOFF)
    q=z+d*v+d*d*a/2
    direction=sign(q.real-arb(1)/4)
    guessed_type={"positive":"Riemann","negative":"dyadic","unresolved":"unresolved"}[direction]
    return dict(row,status="forecast",cutoff_position=pack(z),cutoff_v=pack(v),cutoff_a=pack(a),
                forecasts={"constant":pack(z),"linear":pack(z+d*v),"quadratic":pack(q)},predicted_type=guessed_type)

def terminal(previous,p,radius,tube,disk_check):
    row=previous.copy()
    if row["status"]!="forecast": return row
    try:
        node=advance(row,from_center(row["last_center"]),CUTOFF,END,p,radius,tube)
    except Exhausted as exc:
        return dict(row,status="unresolved",reason=str(exc))
    if not disk_check(node,radius,ball(parameter(END)))[2]:
        return dict(row,status="unresolved",reason="terminal disk isolation")
    return dict(row,status="arrived",center=pack(node),radius=str(radius))

def score(previous,radius):
    row=previous.copy()
    if "probe" in row:
        row["launch_hit"]=(row["predicted_horizontal_side"]==row["measured_horizontal_side"]
                           if "unresolved" not in (row["predicted_horizontal_side"],row["measured_horizontal_side"]) else None)
    if row["status"]!="arrived": return row
    node=from_center(row["last_center"])
    terminal=square(node,radius)
    matches=[]
    for j in range(1,33):
        candidate=acb(0,2*j*arb.pi()/arb(2).log())
        if abs(candidate-node)<radius and not candidate.zeta().contains(0):
            matches.append(("dyadic",j))
    for n in range(1,41):
        candidate=acb.zeta_zero(n)
        if abs(candidate-node)<radius and not (acb(2)**candidate-1).contains(0):
            matches.append(("Riemann",n))
    errors={m:abs(unpack(z)-terminal) for m,z in row["forecasts"].items()}
    primary=sign(arb("0.001")-errors["quadratic"])
    row.update(errors={m:z.str(20) for m,z in errors.items()},
               within_001={"positive":True,"negative":False,"unresolved":None}[primary],
               improvement_sign_vs={m:sign(errors[m]-errors["quadratic"]) for m in ("constant","linear")})
    if len(matches)!=1: return dict(row,status="unresolved",reason="terminal classification")
    kind,index=matches[0]
    return dict(row,status="identified",true_type=kind,index=index,type_hit=(row["predicted_type"]==kind
                if row["predicted_type"]!="unresolved" else None))

def main(args):
    if sha(HERE/"protocol.json")!=PROTOCOL_HASH: raise RuntimeError("Protocol content changed")
    protocol=load(HERE/"protocol.json")
    p=protocol["computation"]
    repo=args.repo.resolve() if args.repo else next(q for q in HERE.parents if (q/"archive/2026-11-19-zero-transport-v001").is_dir())
    src=repo/"archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return"
    sys.path.insert(0,str(src))
    from arithmetic_holdout_replay import centered_tube
    from arithmetic_reference import disk_check
    ctx.prec,ctx.cap=p["precision_bits"],3
    radius=arb(p["disk_radius"])
    work=args.out.resolve()
    work.mkdir(parents=True,exist_ok=True)
    stages=["launch","forecast","terminal","score"]
    ix=stages.index(args.stage)
    key={"protocol_sha256":PROTOCOL_HASH,"stage":args.stage,"working_precision_bits":ctx.prec}
    if ix==0:
        key["public_protocol_commit"]=args.freeze_commit
        if not args.freeze_commit or len(args.freeze_commit)!=40:
            raise RuntimeError("Supply the published pre-evaluation Git commit")
        rows=[launch(k,radius,disk_check) for k in protocol["seeds"]]
    else:
        for j in range(ix):
            earlier=load(work/(stages[j]+".json"))
            assert earlier["stage"]==stages[j] and earlier["protocol_sha256"]==PROTOCOL_HASH
            if j: assert earlier["previous_sha256"]==sha(work/(stages[j-1]+".json"))
        old=earlier["rows"]
        assert [row["k"] for row in old]==protocol["seeds"]
        key["previous_sha256"]=sha(work/(stages[ix-1]+".json"))
        if ix==1: rows=[forecast(r,p,radius,centered_tube) for r in old]
        elif ix==2: rows=[terminal(r,p,radius,centered_tube,disk_check) for r in old]
        else: rows=[score(r,radius) for r in old]
    seal(work/(args.stage+".json"),dict(key,rows=rows))

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("stage",choices=["launch","forecast","terminal","score"])
    a.add_argument("--repo",type=Path)
    a.add_argument("--out",type=Path,default=HERE)
    a.add_argument("--freeze-commit",help="required by launch")
    main(a.parse_args())
