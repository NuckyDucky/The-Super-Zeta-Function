"""Two prospective Dottie clock comparisons. Python 3.12 and python-flint 0.9.0.

Use the Super Zeta repository at ca09c1b1519d441d38dfa7f7152bee6385bfabaf.
python clock_test.py freeze PATH_TO_REPOSITORY    # writes a new protocol.json
python clock_test.py test SHA256_OF_PROTOCOL     # writes a new results.json
Run with assertions enabled. Output goes next to this file.
"""
import hashlib
import json
import platform
import sys
from fractions import Fraction
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq

OUT = Path(__file__).resolve().parent
REVISION = "ca09c1b1519d441d38dfa7f7152bee6385bfabaf"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def ball(value):
    q = Fraction(value)
    return arb(fmpq(q.numerator, q.denominator))

def write_new(name, obj):
    with (OUT / name).open("x", encoding="utf-8", newline="\n") as out:
        json.dump(obj, out, ensure_ascii=False, indent=2)
        out.write("\n")

def orbit_height(x, y):
    return 2 * arb.pi() / (160 * ((ball(x)/ball(y))**2).log1p())

def control(height):
    # Evaluate the adjacent integer grids. The first disjoint one must be among
    # these four: the grid spacing exceeds the sum of the two half-widths.
    floor = int((height / arb.pi()).floor().unique_fmpz())
    candidates = []
    for i in range(floor-1, floor+3):
        distance = abs(i*arb.pi() - height)
        if distance > ball("1/2"):
            candidates.append((i, distance))
        else:
            assert distance < ball("1/2")
    return next(i for i,d in candidates if all(j==i or d < e for j,e in candidates))

def freeze(repo):
    ctx.prec = 384
    src = repo / "archive/2026-11-17-quartet-return-recursion-v001/computations"
    sys.path.insert(0,str(src))
    from dottie_multiplier_winding import return_scale
    y = "0.509892982511772"
    eta = Fraction("4.749479070945369e-8")
    half_box = Fraction("3e-10")
    arms = []
    for direction in (-1,1):
        x = eta + direction*half_box/2
        windings = []
        for vertical in (1,-1):
            for side in (-1,0,1):
                L = acb(side*ball(x), vertical*ball(y))
                for phase,rate in (("P",L),("Q",-L)):
                    scale,k,_ = return_scale(rate)
                    assert scale>0 and abs(k)==1
                    windings.append([vertical,side,phase,k])
        t = orbit_height(x,y)
        n = control(t)
        arms.append(dict(x=str(x), y=y, T=t.str(40), n=n, G=(n*arb.pi()).str(40),
                         separation=abs(t-n*arb.pi()).str(22), windings=windings))
    centers=[h for a in arms for h in (orbit_height(a["x"],y),a["n"]*arb.pi())]
    assert all(abs(t-u)>ball("1/2") for i,t in enumerate(centers) for u in centers[i+1:])
    obj=dict(repository_revision=REVISION, source_sha256={q:digest(src/q) for q in
             ("dottie_multiplier_winding.py","verify_dottie_horn_slice.py")},
             evaluator_sha256=digest(Path(__file__)), pyflint=flint.__version__,
             flint=flint.__FLINT_VERSION__, python=platform.python_version(),
             nomination="Two transverse magnitudes eta plus/minus half of the published box half-width (3e-10); same y, primitive scalar period 320, both rooted winds of absolute value 1. Exact height is 2*pi/(160*log1p((x/y)^2)).",
             control="Nearest pi*n whose closed window is disjoint from its paired clock window. All four half-widths = 1/4 in Riemann height.",
             prediction="New pilot hypothesis: both Dottie centers are strictly closer to a nontrivial Riemann zero ordinate than their respective grid controls. Distance is censored at 1/4. One win is mixed, two losses favor the grid. Report ties and unresolved pairs; no replacement cases or tuning.",
             method="Use the full count N(H) and the adjacent indexed ordinates, then minimize the two directed distances, censored at 1/4. Primary statistic counts Dottie wins, comparing distances in raw Riemann height units within each matched pair. No claim of global significance. This is a proximity test, not a prediction of an off-line zero.",
             budget="Two nominated and two control centers. Per center one global count and one batch of two indexed zeros at 96 bits. If a bound or count is ambiguous, allow one retry at 160 bits; report unresolved if ambiguous again. No alternative statistic.",arms=arms)
    write_new("protocol.json",obj)
    print("Protocol sha256:",digest(OUT/"protocol.json"))
    for a in arms: print("x",a["x"],"T",a["T"],"grid n",a["n"],"G",a["G"])

def distance(arm, is_grid):
    for bits in (96,160):
        ctx.prec=bits
        h=arm["n"]*arb.pi() if is_grid else orbit_height(arm["x"],arm["y"])
        count=h.zeta_nzeros().unique_fmpz()
        if count is None: continue
        lower,upper=acb.zeta_zeros(count,2)
        distances=[h-lower.imag, upper.imag-h, ball("1/4")]
        if not all(d>0 for d in distances): continue
        for index,d in enumerate(distances):
            if all(i==index or d < other for i,other in enumerate(distances)):
                return d,dict(center=h.str(35),N=int(count), indices=[int(count),int(count)+1],
                              adjacent_zeros=[str(lower),str(upper)], distance=d.str(22),
                              closest=("lower","upper","censored")[index], bits=bits)
    return None,dict(closest="unresolved")

def test(key):
    planfile=OUT/"protocol.json"
    assert key==digest(planfile)
    plan=json.loads(planfile.read_bytes())
    assert digest(Path(__file__))==plan["evaluator_sha256"]
    results=[]
    for arm in plan["arms"]:
        d,ds=distance(arm,False)
        g,gs=distance(arm,True)
        if d is None or g is None: result="unresolved"
        elif d < g: result="Dottie"
        elif g < d: result="grid"
        elif ds["closest"]==gs["closest"]=="censored": result="tie"
        else: result="unresolved"
        results.append(dict(x=arm["x"],Dottie=ds,grid=gs,closer=result))
        print(result,ds.get("distance"),gs.get("distance"),flush=True)
    write_new("results.json",dict(protocol_sha256=key,pairs=results))
if __name__=="__main__":
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    if len(sys.argv)==3 and sys.argv[1]=="freeze": freeze(Path(sys.argv[2]).resolve())
    elif len(sys.argv)==3 and sys.argv[1]=="test": test(sys.argv[2])
    else: raise SystemExit(__doc__)

