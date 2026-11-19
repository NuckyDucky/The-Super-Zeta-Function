"""Given recovered Hurwitz shifts, invert the original calibrated right flank.

Python 3.12 and python-flint 0.9.0. Stage 'recover' reads only the recovered
shift and the published branch calibration. Stage 'score' checks the visits.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx


HERE = Path(__file__).resolve().parent


from layout import OUTPUT


def boxes(z):
    return {"real": z.real.str(27), "imag": z.imag.str(27)}


def log_mu_derivative(f, left, right, orbit):
    """Implicit derivative of the rooted periodic point; complex derivative of log(mu) in y."""
    L = acb(f.real(f.ETA), f.real(left).union(f.real(right)))
    z,r = orbit["p"],orbit["r"]
    stages = []
    velocity = (acb(0),arb(0))
    for k in range(320):
        for sign in (-1,1):
            before = f.box(z,r)
            z,r = f.stage(z,r,sign*L)
            after = f.box(z,r)
            gain,offset = sign*L*after, acb(0,sign)*before*after
            velocity = f.affine(velocity,gain,offset)
            stages.append((sign,before,gain,offset))
    # Differentiate p=G_L(p), then propagate dp/dy around the same lap.
    velocity = f.disc(f.box(*velocity)/(1-orbit["mu"]))
    derivative = 640*acb(0,1)/L
    for sign,before,gain,offset in stages:
        derivative += acb(0,sign)*before+sign*L*f.box(*velocity)
        velocity = f.affine(velocity,gain,offset)
    assert derivative.imag > 0
    slope = -derivative.real / (derivative.imag*180/arb.pi())
    return slope


def invert_angle(f, theta, lo, hi, slope_lower):
    a,b = f.tinybracket(1,theta.mid(),lo,hi)
    # |dy| <= |dtheta| / min(dtheta/dy) on the calibrated branch.
    margin = Fraction(str((2*theta.rad().upper()/slope_lower).upper().fmpq())) + Fraction(1,10**55)
    a,b = a-margin,b+margin
    assert lo <= a < b <= hi
    assert f.moment(1,a,a,False)["a"] < theta < f.moment(1,b,b,False)["a"]
    return a,b


def recover(f, b, lo, hi, slope_lower):
    theta = 90-180*b
    assert theta>45 and theta<60
    yl,yh = invert_angle(f,theta,lo,hi,slope_lower)
    orbit = f.moment(1,yl,yh,False)
    L, pd, qd = f.ordered_root(1,yl,yh)
    assert abs(orbit["mu"]) < 1
    slope = log_mu_derivative(f,yl,yh,orbit)
    return {"b": b.str(26), "native_angle": theta.str(26),
            "ReL": str(f.ETA), "ImL": f.stamp((yl,yh)),
            "P": boxes(f.box(*pd)), "Q": boxes(f.box(*qd)),
            "multiplier": boxes(orbit["mu"]), "abs_multiplier": abs(orbit["mu"]).str(26),
            "d_log_abs_mu_per_clockwise_degree": slope.str(26),
            "trapping_disk_lipschitz_upper": orbit["k"].upper().str(20),
            "period_divisor_exclusion": orbit["gap"].lower().str(20)}


def sweep(f, lo, hi):
    """Cover the full 60-to-45 degree sweep and bound the rate of contraction."""
    boundaries = [f.tinybracket(1,arb(theta),lo,hi) for theta in (45,60)]
    left,right = boundaries[0][0],boundaries[1][1]
    terminal,initial = [abs(f.moment(1,a,b,False)["mu"]) for a,b in boundaries]
    pending = [(max(a,left),min(b,right)) for a,b,_ in f.CHARTS[1] if max(a,left)<min(b,right)]
    n = 0
    merged = None
    while pending:
        a,b=pending.pop()
        try:
            native=f.moment(1,a,b,False)
            slope=log_mu_derivative(f,a,b,native)
            ok = slope.is_finite() and slope<0 and slope.rad()<arb("0.0005")
        except (AssertionError,ArithmeticError):
            ok = False
        if not ok:
            if b-a<Fraction(1,10**15):
                raise ArithmeticError("Uniform sign unresolved")
            m=(a+b)/2
            pending.extend(((a,m),(m,b)))
            continue
        merged=slope if merged is None else merged.union(slope)
        n+=1
    return {"clockwise_turn_degrees":[0,15],"native_angles_degrees":[60,45],"cells":n,
            "d_log_abs_mu_per_clockwise_degree":{"lower":merged.lower().str(18),"upper":merged.upper().str(18)},
            "initial_abs_mu":initial.str(18),"terminal_abs_mu":terminal.str(18),
            "relative_decrease":(1-terminal/initial).str(18)}


def configure(repo):
    arch=repo.resolve()/"archive"
    sys.path[:0]=[str(arch/"2026-11-19-oriented-return-v001"/"computations"),
                  str(arch/"2026-11-19-zero-transport-v001"/"Dottie-Off-Axis-Return")]
    import flank_path as f
    from orbit_crossing import advance, stage
    from quarter_probe import degree
    from verify_dottie_horn_slice import trapping_data
    f.advance,f.stage,f.degree,f.trapping_data=advance,stage,degree,trapping_data
    return f


def main():
    if not __debug__:
        raise RuntimeError("Enable assertions")
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("action",choices=["recover","score","sweep","collision"])
    p.add_argument("--repo",type=Path,required=True)
    p.add_argument("--decoded",type=Path,default=OUTPUT/"decoded.json")
    p.add_argument("--out",type=Path)
    p.add_argument("--truth",type=Path,default=HERE/"scoring"/"truth.json")
    args=p.parse_args()
    ctx.prec,ctx.cap=448,5
    if args.action=="score":
        got=json.loads((args.out or OUTPUT/"recovered-orbits.json").read_bytes())
        truth=json.loads(args.truth.read_bytes())["readouts_in_packet_order"]
        ids=[]
        for row in got["recovered"]:
            matches=[t for t in truth if arb(row["ImL"]["interval"]).overlaps(arb(t["ImL"]["interval"]))]
            assert len(matches)==1
            target=matches[0]
            ids.append(target["visit"])
            assert arb(row["abs_multiplier"]).overlaps(arb(target["abs_multiplier"]))
        assert sorted(ids)==[1,2]
        print("Scored decoded input order:",ids)
        return
    f=configure(args.repo)
    # A predecessor verifier sets its own default on import.
    ctx.prec,ctx.cap=448,5
    lo,hi,cal=f.calibration(1)
    if args.action=="sweep":
        record=sweep(f,lo,hi)
        record["precision_bits"]=ctx.prec
        dest=OUTPUT/"contraction-sweep.json"
    else:
        if args.action=="collision":
            angles=json.loads((OUTPUT/"chart-crossing.json").read_bytes())["bounds"]
            shifts=[arb(1)/6+arb(angles[k])/180 for k in ("h1","h2")]
            dest=OUTPUT/"collision-orbits.json"
        else:
            decoded=json.loads(args.decoded.read_bytes())
            if isinstance(decoded,dict):
                decoded=decoded["entries"]
            shifts=[arb(row["b"]) for row in decoded]
            dest=OUTPUT/"recovered-orbits.json"
        record={"precision_bits":ctx.prec,"chart":"continued original right-flank period-640, rooted first phase",
                "primitive_scalar_period":320,"paired_period":640,"calibration":cal,
                "recovered":[recover(f,b,lo,hi,arb(cal["slope_abs_lower"])) for b in shifts]}
        if args.action=="collision":
            first,second=[arb(row["abs_multiplier"]) for row in record["recovered"]]
            assert first>second
    (args.out or dest).write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
    print(record,flush=True)


if __name__=="__main__":
    main()
