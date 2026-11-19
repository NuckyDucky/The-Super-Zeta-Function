"""Directed jets of the sixth landing at three passes and two folds. Python 3.12, python-flint 0.9.0."""
import argparse
import hashlib
import json
from bisect import bisect_right
from fractions import Fraction as F
from pathlib import Path
import sys

from flint import acb, acb_series, arb, ctx

HERE = Path(__file__).resolve().parent
BASE = F(1, 6)
TARGET = F(149, 4)
COLS = ["alpha", "sigma", "T", "sigma1", "T1", "sigma2", "T2"]
BRACKETS = [
    ("pass1", "10.16008865", "10.16008872", 1),
    ("maximum", "10.95490542", "10.95490549", -1),
    ("pass2", "12.32133502", "12.32133509", -1),
    ("minimum", "13.40917355", "13.40917366", 1),
    ("pass3", "14.10170455", "14.10170464", 1),
]


def source_root(override):
    if override is not None:
        return Path(override).resolve()
    siblings = HERE.parent.parent
    for root in (siblings / "2026-11-19-zero-transport-v001", siblings):
        if (root / "Dottie-Transport-Reversibility" / "rho6-replay.json").is_file():
            return root
    raise FileNotFoundError("Supply --archive pointing to the 2026-11-19-zero-transport-v001 snapshot.")


def ball(q):
    return arb(q.numerator) / q.denominator


def square(center, radius):
    return center + acb(arb(0, radius), arb(0, radius))


def jets(z, b):
    """Implicit complex derivatives with respect to positive CLOCKWISE DEGREES."""
    w = acb_series([z, 1], 3)
    h = w.zeta(b) + w.zeta(1-b)
    hb = -w * ((w+1).zeta(b) - (w+1).zeta(1-b))
    hbb = z*(z+1) * ((z+2).zeta(b) + (z+2).zeta(1-b))
    v = -hb[0] / h[1]
    acc = -(hbb + 2*hb[1]*v + 2*h[2]*v*v) / h[1]
    return v/180, acc/(180**2)


def sgn(x):
    if x>0: return 1
    if x<0: return -1
    raise ArithmeticError(f"Unresolved sign: {x}")


class Branch:
    def __init__(self, archive):
        sys.path.insert(0, str(archive / "Dottie-Off-Axis-Return"))
        from arithmetic_braid import shrink_root
        from arithmetic_reference import disk_check
        from arithmetic_holdout_replay import centered_tube
        self.shrink_root = shrink_root
        self.disk_check = disk_check
        self.centered_tube = centered_tube
        self.radius = arb("1e-30")
        witness = archive / "Dottie-Transport-Reversibility" / "rho6-replay.json"
        blob = witness.read_bytes()
        self.digest = hashlib.sha256(blob).hexdigest()
        record = json.loads(blob)
        self.knots = [F(p["shift"]) for p in record["checkpoints"]]
        self.boxes = [acb(arb(p["zero"]["real"]),arb(p["zero"]["imag"])) for p in record["checkpoints"]]
        self.tight = {}
        assert self.knots == sorted(self.knots) and (self.knots[0],self.knots[-1]) == (BASE,F(1,4))
        seed=acb(0,12*arb.pi()/arb(3).log())
        assert abs(self.boxes[0]-seed) < arb("1e-9")
        assert disk_check(seed.mid(),arb("1e-9"),ball(BASE))[2]
        assert abs(self.boxes[-1]-acb.zeta_zero(6)) < arb("1e-9")
        assert disk_check(acb.zeta_zero(6).mid(),arb("1e-9"),ball(F(1,4)))[2]

    def walk(self, node, a, b):
        if a==b: return node
        proof = self.centered_tube(node,self.radius,a,b)
        if proof is not None: return proof[0]
        assert abs(b-a)>F(1,2**65)
        m=(a+b)/2
        return self.walk(self.walk(node,a,m),m,b)

    def at(self, b):
        i=bisect_right(self.knots,b)-1
        assert 0<=i<len(self.knots) and self.knots[0]<=b<=self.knots[-1]
        a=self.knots[i]
        if i not in self.tight:
            old=self.boxes[i]
            node=self.shrink_root(old.mid(),ball(a),3)
            assert abs(old-node) < arb("1e-9")
            assert self.disk_check(node,arb("1e-9"),ball(a))[2]
            assert self.disk_check(node,self.radius,ball(a))[2]
            self.tight[i]=node
        return self.walk(self.tight[i],a,b)

    def enclose(self,a,b):
        proof=self.centered_tube(self.at(a),self.radius,a,b)
        assert proof is not None
        _,_,r,c=proof
        return square(c,r)

    def node_values(self,b):
        w=square(self.at(b),self.radius)
        v,acc=jets(w,ball(b))
        return w,v,acc

    def event(self,name,lo,hi,direction):
        a,b=[BASE+F(x)/180 for x in (lo,hi)]
        is_pass=name.startswith("pass")
        def value(param):
            w,v,_=self.node_values(param)
            return w.imag-ball(TARGET) if is_pass else v.imag
        assert sgn(value(a))==-direction and sgn(value(b))==direction
        box=self.enclose(a,b)
        v,acc=jets(box,ball(a).union(ball(b)))
        # The local sign change has exactly one solution inside this bracket.
        assert sgn(v.imag if is_pass else acc.imag)==direction
        for _ in range(47):
            m=(a+b)/2
            if sgn(value(m))==direction: b=m
            else: a=m
        span=ball(a).union(ball(b))
        w=self.enclose(a,b)
        if is_pass:
            assert w.imag.contains(ball(TARGET))
            w=acb(w.real,ball(TARGET))
        v,acc=jets(w,span)
        if not is_pass:
            assert v.imag.contains(0) and sgn(v.real)!=0
            v=acb(v.real,0)
        speed=abs(v)
        signed_curve=(v.conjugate()*acc).imag/(speed**3)
        Y_T=-v.real/v.imag if is_pass else None
        Y_TT=(v.real*acc.imag-acc.real*v.imag)/(v.imag**3) if is_pass else None
        entries=dict(alpha=180*(span-ball(BASE)),sigma=w.real,T=w.imag,sigma1=v.real,T1=v.imag,
                     sigma2=acc.real,T2=acc.imag,speed=speed,Y_T=Y_T,Y_TT=Y_TT,curvature=signed_curve)
        return dict(id=name,bounds={k:x.str(21) if x is not None else None for k,x in entries.items()},
                    mid={k:float(x.mid()) if x is not None else None for k,x in entries.items()})

    def count_passes(self,events):
        """Cover the complete parameter range. Certify zero or one level passage per leaf."""
        target=ball(TARGET)
        arc_angles=(F(645,64),F(905,64))
        arc_left,arc_right=(BASE+angle/180 for angle in arc_angles)
        low,high=arb('37.2158'),arb('37.3132')
        band=low.union(high)
        certified_exterior={"height_excludes_band":0,"height_derivative_positive":0}
        for event in events:
            if event['id'] in ('minimum','maximum'):
                theta=arb(event['bounds']['alpha'])
                height=arb(event['bounds']['T'])
                assert ball(arc_angles[0])<theta and theta<ball(arc_angles[1])
                assert low<height and height<high
        count=0
        brackets=[]
        node=self.at(BASE)
        assert node.imag+arb(0,self.radius)<low
        for i,(left,right) in enumerate(zip(self.knots,self.knots[1:]),start=1):
            pending=[(left,right)]
            while pending:
                a,b=pending.pop()
                tube=self.centered_tube(node,self.radius,a,b)
                if tube is not None:
                    end,_,r,c=tube
                    height=c.imag+arb(0,r)
                    exterior=(a<arc_left or b>arc_right)
                    touches_band=exterior and height.overlaps(band)
                    includes_target=height.contains(target)
                    if not touches_band and not includes_target:
                        if exterior:
                            certified_exterior['height_excludes_band']+=1
                        node=end
                        count+=1
                        continue
                    w=square(c,r)
                    span=ball(a).union(ball(b))
                    s=acb_series([w,1],2)
                    denom=(s.zeta(span)+s.zeta(1-span))[1]
                    v=w*((w+1).zeta(span)-(w+1).zeta(1-span))/denom
                    if not v.imag.contains(0) and v.imag.is_finite() and (not touches_band or v.imag>0):
                        sl=sgn(node.imag+arb(0,self.radius)-target)
                        sr=sgn(end.imag+arb(0,self.radius)-target)
                        if sl!=sr:
                            assert sgn(v.imag)==sr
                            brackets.append([str(180*(a-BASE)),str(180*(b-BASE)),sr])
                        if touches_band:
                            certified_exterior['height_derivative_positive']+=1
                        node=end
                        count+=1
                        continue
                assert b-a>F(1,2**40)
                m=(a+b)/2
                pending.extend([(m,b),(a,m)])
            # Every independently refined checkpoint used by the event calculation
            # represents this same continued branch. Both tiny disks fit inside
            # one larger disk containing a unique zero at this exact parameter.
            checkpoint=self.at(right)
            shared=arb("1e-9")
            assert abs(checkpoint-node)+self.radius < shared
            assert abs(self.boxes[i]-node) < shared
            assert self.disk_check(node,shared,ball(right))[2]
        assert abs(node-acb.zeta_zero(6))<arb("1e-9")
        assert node.imag+arb(0,self.radius)>high
        assert len(brackets)==3
        for (l,r,d),event in zip(brackets,[e for e in events if e["id"].startswith("pass")]):
            x=arb(event["bounds"]["alpha"])
            assert ball(F(l))<x and x<ball(F(r)) and d==sgn(arb(event["bounds"]["T1"]))
        return {"full_sweep_degrees":[0,15],"accepted_cells":count,"passage_count":3,
                "isolating_angle_intervals_and_directions":brackets,
                "band_certificate":{"outer_height_band":["37.2158","37.3132"],
                    "interior_arc_degrees":[str(x) for x in arc_angles],
                    "exterior_cells":certified_exterior,
                    "initial_height_below_and_terminal_height_above_band":True,
                    "interior_stationary_heights_verified_by":"turning.py"}}


def run(archive):
    ctx.prec,ctx.cap=192,3
    branch=Branch(archive)
    events=[branch.event(*v) for v in BRACKETS]
    census=branch.count_passes(events)
    rows=[]
    for j in range(390,581):
        angle=F(j,40)
        w,v,acc=branch.node_values(BASE+angle/180)
        rows.append([float(angle),*(float(x.mid()) for x in [w.real,w.imag,v.real,v.imag,acc.real,acc.imag])])
    return dict(precision_bits=ctx.prec, angle_unit="positive clockwise degree from the 60 degree anchor",
                rotated_coordinates=["T","1/2-sigma"],height=str(TARGET),
                source_file="Dottie-Transport-Reversibility/rho6-replay.json",
                source_sha256=branch.digest, full_sweep_census=census,events=events,columns=COLS,profiles=rows)


def compare(new,old):
    for key in ("precision_bits","angle_unit","rotated_coordinates","height","source_file","source_sha256","columns"):
        assert new[key]==old[key],key
    assert new["full_sweep_census"]["passage_count"]==old["full_sweep_census"]["passage_count"]==3
    for key in ('outer_height_band','interior_arc_degrees','initial_height_below_and_terminal_height_above_band','interior_stationary_heights_verified_by'):
        assert new['full_sweep_census']['band_certificate'][key]==old['full_sweep_census']['band_certificate'][key],key
    nev,oev=new["events"],old["events"]
    assert len(nev)==len(oev)==5
    for event,other in zip(nev,oev):
        assert event["id"]==other["id"] and event["bounds"].keys()==other["bounds"].keys()
        for k,s in event["bounds"].items():
            t=other["bounds"][k]
            if s is None: assert t is None
            else: assert arb(s).overlaps(arb(t)),(event["id"],k,s,t)
        for k,v in event["mid"].items():
            vref=other["mid"][k]
            assert (vref is None if v is None else abs(v-vref)<1e-10),(event["id"],k)
    assert len(new["profiles"])==len(old["profiles"])==191
    for row,other in zip(new["profiles"],old["profiles"]):
        assert len(row)==len(other)==len(COLS) and all(abs(x-y)<1e-10 for x,y in zip(row,other))


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Run with assertions enabled.")
    parser=argparse.ArgumentParser(__doc__)
    parser.add_argument("--archive",type=Path)
    parser.add_argument("--output",type=Path,default=HERE/"jets.json")
    parser.add_argument("--compare",type=Path)
    args=parser.parse_args()
    result=run(source_root(args.archive))
    if args.compare:
        compare(result,json.loads(args.compare.read_bytes()))
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    for e in result["events"]:
        print(e["id"],e["mid"],flush=True)
