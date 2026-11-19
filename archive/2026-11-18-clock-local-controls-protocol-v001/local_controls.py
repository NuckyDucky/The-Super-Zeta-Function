"""Prospective 32-witness test for the reciprocal-tetration clock.
Requires Python 3.12 and python-flint 0.9.0. Use a fresh working directory.
  python local_controls.py freeze
  python local_controls.py orbits PATH_TO_REPO PROTOCOL_SHA
  python local_controls.py zeros PROTOCOL_SHA
Outputs go in the current directory. Assertions must be enabled. No randomness.
"""
import hashlib
import json
import sys
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq

Y = "0.509892982511772"
ETA = Fraction("4.749479070945369e-8")
W = Fraction("3e-10")
UPSTREAM = Path("archive/2026-11-17-quartet-return-recursion-v001/computations")
REV = "ca09c1b1519d441d38dfa7f7152bee6385bfabaf"
STAGES = ((384,48), (768,96), (1536,144))
WORKERS = 3

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def record(path, data):
    with Path(path).open("x", encoding="utf-8", newline="\n") as out:
        json.dump(data, out, indent=2, ensure_ascii=True)
        out.write("\n")

def read(path):
    return json.loads(Path(path).read_bytes())

def ball(x):
    q = Fraction(x)
    return arb(fmpq(q.numerator, q.denominator))

def centers(x):
    h = 2*arb.pi() / (160*((ball(x)/ball(Y))**2).log1p())
    separation = 8*arb.pi() / (h/(2*arb.pi())).log()
    return [h-separation, h, h+separation]

def freeze():
    ctx.prec=160
    xs=[ETA+Fraction(2*j-33,32)*W for j in range(1,33)]
    assert len(set(xs))==32 and all(abs(x-ETA)<W for x in xs)
    assert all(x not in (ETA,ETA-W/2,ETA+W/2) for x in xs)
    rr=[{"j":j, "x":str(x), "centers_left_clock_right":[v.str(32) for v in centers(x)]}
        for j,x in enumerate(xs,1)]
    cc=sorted([h for x in xs for h in centers(x)],key=lambda h:float(h))
    assert all(b-a>ball("1/2") for a,b in zip(cc,cc[1:]))
    # Verify the new windows avoid both previous pilot arms, the original
    # clock and its matched grid, and the original second and third harmonics.
    old=[centers(ETA)[1],2*centers(ETA)[1],3*centers(ETA)[1],
         centers(ETA-W/2)[1],centers(ETA+W/2)[1]]
    old += [n*arb.pi() for n in (1440708526392,1449852029395,1431651246793)]
    assert all(abs(h-t)>2 for h in cc for t in old)
    record("protocol.json",dict(evaluator_sha256=sha(__file__), source_commit=REV,
        python_flint=flint.__version__,flint=flint.__FLINT_VERSION__,y=Y,
        parameter_rule="All 32 midpoints x_j=eta+((2j-33)/32)*3e-10, j=1,...,32, in the published transverse box at one y. Positive x is a magnitude; its reflected addresses are retained. No substitutions.",
        clock="Cap=1. Primitive scalar period=320. Both rooted tangent windings have absolute value one for both flank signs and their midpoint; lower half-plane by complex conjugation. H=2*pi/(160*log1p((x/y)^2)).",
        controls="Left and right controls H plus/minus 4 local smooth mean spacings, spacing=2*pi/log(H/(2*pi)). All 96 windows are disjoint, equal half-width 1/4. This replaces the earlier pi-grid comparison and explicitly tests local sensitivity of the nominated center.",
        prediction="A majority of the 64 matched comparisons favor the clock. Primary score is (wins + ties/2)/64. Benchmark 1/2. Greater favors the clock on these inputs; smaller favors shifted controls; equality even. No analysis based on independent Bernoulli trials. Also print win/tie/loss/unresolved and witness-level outcomes.",
        censoring="Use d(H)=min(1/4, min abs(H-gamma) over positive ordinates of nontrivial zeros). Compare directed enclosures. Exact equal censored distances tie. A vote unresolved by the budget contributes [0,1] to the all-32 score. Report resolved-only as descriptive if different. Predictive success requires lower bound >1/2.",
        orbit_budget="First 384 bits and 48 cap laps, then 768/96 and 1536/144 only if needed. Same trapping radius, divisor exclusions and tangent lifts as original verifier. Check center and both flanks for P and Q, lower half-plane follows by conjugation. Unresolved cases keep their two votes in the denominator and receive no zero search.",
        zero_budget="For each eligible center use FLINT's N(H) plus the consecutive zeros of indices N(H) and N(H)+1. Initial 96 bits; retry at 160 if an index, side, distance, or pair comparison is unresolved. No other heights or outcome metrics. At most 3 workers.",
        witnesses=rr))
    print("protocol",sha("protocol.json"))

def check_inputs(key):
    assert key==sha("protocol.json")
    plan=read("protocol.json")
    assert plan["evaluator_sha256"]==sha(__file__)
    return plan

def certify_orbit(args):
    repo,j,x=args
    src=Path(repo)/UPSTREAM
    if str(src) not in sys.path: sys.path.insert(0,str(src))
    import verify_dottie_horn_slice as trap
    from dottie_multiplier_winding import return_scale
    marks=[]
    failures=[]
    for side in (0,-1,1):
        for phase in ("P","Q"):
            passed=False
            for bits,laps in STAGES:
                ctx.prec=bits
                trap.BLOCKS=laps
                L=acb(side*ball(x),ball(Y))
                try:
                    scale,k,_=return_scale(L if phase=="P" else -L)
                    if abs(k)!=1:
                        return dict(j=j,x=x,status="nonunit winding",side=side,phase=phase,k=k,marks=marks)
                    assert scale>0
                    marks.append(dict(side=side,phase=phase,k=k,bits=bits,cap_laps=laps))
                    passed=True
                    break
                except (ArithmeticError,AssertionError,ValueError) as exc:
                    failures.append(dict(side=side,phase=phase,bits=bits,reason=str(exc)))
            if not passed:
                return dict(j=j,x=x,status="unresolved",marks=marks,attempts=failures)
    return dict(j=j,x=x,status="certified",marks=marks,attempts=failures)

def orbits(repo,key):
    plan=check_inputs(key)
    params=[(repo,row["j"],row["x"]) for row in plan["witnesses"]]
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        result=list(pool.map(certify_orbit,params))
    record("orbits.json",dict(protocol=key,rows=result))
    print(Counter(r["status"] for r in result),flush=True)

def nearest(h):
    n=h.zeta_nzeros().unique_fmpz()
    if n is None: return None,{"status":"ambiguous count"}
    a,b=acb.zeta_zeros(n,2)
    ds=[h-a.imag,b.imag-h,ball("1/4")]
    if all(d>0 for d in ds):
        for i,d in enumerate(ds):
            if all(i==j or d<e for j,e in enumerate(ds)):
                return d,dict(status=("lower","upper","censored")[i],N=int(n),
                    center=h.str(32),adjacent_zeros=[str(a),str(b)],distance=d.str(25))
    return None,dict(status="ambiguous distance")

def vote(clock, other, c_rec, o_rec):
    if clock is None or other is None: return "unresolved"
    if clock < other: return "win"
    if other < clock: return "loss"
    if c_rec["status"]==o_rec["status"]=="censored": return "tie"
    return "unresolved"

def trial(row):
    if row["status"]!="certified":
        return dict(j=row["j"],orbit_status=row["status"],votes=["unresolved"]*2)
    for bits in (96,160):
        ctx.prec=bits
        calc=[nearest(h) for h in centers(row["x"])]
        distances,records=zip(*calc)
        votes=[vote(distances[1],distances[k],records[1],records[k]) for k in (0,2)]
        if "unresolved" not in votes: break
    return dict(j=row["j"],orbit_status=row["status"],bits=bits,votes=votes,
                locations=dict(zip(("left","clock","right"),records)))

def zeros(key):
    plan=check_inputs(key)
    orbs=read("orbits.json")
    assert orbs["protocol"]==key
    assert [(j["j"],j["x"]) for j in orbs["rows"]]==[(j["j"],j["x"]) for j in plan["witnesses"]]
    result=[]
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        for row in pool.map(trial,orbs["rows"]):
            result.append(row)
            print(row["j"],row["votes"],flush=True)
    counts=Counter(v for r in result for v in r["votes"])
    assert sum(counts.values())==64
    credit=Fraction(counts["win"])+Fraction(counts["tie"],2)
    limits=[str(credit/64),str((credit+counts["unresolved"])/64)]
    record("results.json",dict(protocol=key,orbits_sha256=sha("orbits.json"),
        totals=dict(counts),score_interval=limits,rows=result))
    print("votes",counts,"score interval",limits)

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    cmd=sys.argv[1:]
    if cmd==["freeze"]: freeze()
    elif len(cmd)==3 and cmd[0]=="orbits": orbits(str(Path(cmd[1]).resolve()),cmd[2])
    elif len(cmd)==2 and cmd[0]=="zeros": zeros(cmd[1])
    else: raise SystemExit(__doc__)

