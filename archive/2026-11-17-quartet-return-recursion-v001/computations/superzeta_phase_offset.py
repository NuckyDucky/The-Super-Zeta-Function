"""High-height phase sum in the continued odd cosine spectrum and its dyadic copies.

Predict uses a standard Riemann--Siegel main sum and its leading correction.
Check uses independent ball evaluation at the recorded endpoints. Run with
Python, python-flint and numpy. Both heights and all offsets use separate
coordinates, so a small offset is never rounded into a 13-digit machine float.
"""

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parent/"deps"))
from flint import acb, arb, ctx


LEVELS = (954985468715,954985468716)
HALF_WIDTH = Fraction(1,20_000_000)


def as_ball(q):
    return arb(q.numerator)/q.denominator


def theta(t):
    return acb(arb(1)/4,t/2).lgamma().imag-t*arb.pi().log()/2


def unit(angle):
    z = acb(0,angle).exp()
    return complex(float(z.real.mid()),float(z.imag.mid()))


def phase_sum(n):
    t0 = n*arb.pi()
    th0 = theta(t0)
    limit = int((t0/(2*arb.pi())).sqrt().floor().unique_fmpz())
    assert ((t0+1)/(2*arb.pi())).sqrt().floor().unique_fmpz() == limit
    odd = np.arange(1,limit+1,2)
    # The distinct reference roots are pi*(2j-1)/2. Removing pi/2
    # gives the positive odd integers. The phase of each is initialized
    # with ball arithmetic before conversion to a double-precision phasor.
    base = np.fromiter((unit(th0-t0*arb(int(m)).log()) for m in odd),
                       dtype=np.complex128,count=len(odd))
    phases = np.empty(limit,dtype=np.complex128)
    phase_two = unit(-t0*arb(2).log())
    power_two, rotation = 1, 1+0j
    while power_two<=limit:
        count = (limit//power_two+1)//2
        phases[power_two-1::2*power_two] = rotation*base[:count]
        power_two, rotation = 2*power_two, rotation*phase_two
    modes = np.arange(1,limit+1,dtype=np.float64)
    weighted = phases/np.sqrt(modes)
    logs = np.log(modes)

    def value(d):
        t = t0+as_ball(d)
        scale = (t/(2*arb.pi())).sqrt()
        p = float((scale-limit).mid())
        # None of this experiment's points are near the removable 0/0 cases.
        assert abs(math.cos(2*math.pi*p)) > 0.01
        c0 = math.cos(2*math.pi*(p*p-p-1/16))/math.cos(2*math.pi*p)
        correction = (-1)**(limit-1)*c0/math.sqrt(float(scale.mid()))
        motion = np.exp((-1j*float(d))*logs)
        return 2*(unit(theta(t)-th0)*np.sum(weighted*motion)).real+correction
    return limit,value


def predict(n):
    count,value = phase_sum(n)
    lo = Fraction(0)
    left = value(lo)
    for j in range(1,33):
        hi = Fraction(j,32)
        right = value(hi)
        if left*right < 0:
            break
        lo,left = hi,right
    else:
        raise ValueError("No sign change in the predetermined scan")
    for _ in range(29):
        mid = (lo+hi)/2
        if left*value(mid)>0:
            lo=mid
        else:
            hi=mid
    center = (lo+hi)/2
    return {"level":n,"modes":count,"estimated_offset":float(center),
            "offset_interval":[str(center-HALF_WIDTH),str(center+HALF_WIDTH)]}


def check(record):
    t0 = record["level"]*arb.pi()
    def z(d):
        h = t0+d
        result = acb(0,theta(h)).exp()*acb(arb(1)/2,h).zeta()
        assert result.imag.contains(0)
        return result.real
    lo,hi = [as_ball(Fraction(q)) for q in record["offset_interval"]]
    left,right = z(lo),z(hi)
    assert left*right<0
    print("level",record["level"],"Hardy endpoint signs",left.str(8),right.str(8),flush=True)
    for _ in range(20):
        mid = (lo+hi)/2
        val = z(mid)
        if left*val>0:
            lo,left=mid,val
        else:
            assert right*val>0
            hi,right=mid,val
    print("certified offset",lo.union(hi).str(22),flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode",choices=["predict","check"])
    p.add_argument("record",type=Path)
    args = p.parse_args()
    ctx.prec = 160
    if args.mode == "predict":
        results = [predict(n) for n in LEVELS]
        with args.record.open("x",encoding="utf-8",newline="\n") as out:
            out.write(json.dumps(results,indent=2)+"\n")
        print(json.dumps(results,indent=2))
    else:
        print("Checking SHA-256",hashlib.sha256(args.record.read_bytes()).hexdigest(),flush=True)
        for item in json.loads(args.record.read_text(encoding="utf-8")):
            check(item)
