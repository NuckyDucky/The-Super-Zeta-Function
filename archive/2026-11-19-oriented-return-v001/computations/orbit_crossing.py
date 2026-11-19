"""Native opposing 30-degree return angles along the original Dottie centerline.

Uses the archived disk arithmetic from the Super Zeta Function repository. The
full parameter interval and both narrow boxes below have exact rational ends.
Outputs a recalculable JSON certificate under Python 3.12, python-flint 0.9.0.
"""
from fractions import Fraction
import json
import sys
from pathlib import Path

from flint import arb, acb, ctx


def rational(text):
    q = Fraction(text)
    return arb(q.numerator)/q.denominator


ARCHIVE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ARCHIVE / "2026-11-17-quartet-return-recursion-v001/computations"))
from verify_dottie_horn_slice import advance, stage

BRANCH_START = Fraction("0.50989298230")
BRANCH_END = Fraction("0.50989298314")
SLOPE_MIN = 180000000000
SLOPE_MAX = 193000000000


def verify():
    if not __debug__:
        raise RuntimeError("Run Python with assertions enabled.")

    ctx.prec = 448
    unit = acb(0,1)
    period, radius = 320, rational("1e-15")
    endpoints = ["0.50989298230","0.50989298315"]
    whole = rational(endpoints[0]).union(rational(endpoints[1]))
    c, r, bound, subdiv = advance(acb(1), radius, unit*whole, period, monitor=True)
    image = (abs(c-1)+r).upper()
    assert image < radius and bound < 1
    div_gap = {k:(abs(pt-1)-rad-radius).lower() for k,(pt,rad) in subdiv.items()}
    assert set(div_gap) == {160,64} and all(v>0 for v in div_gap.values())

    def box(disc):
        mid, rad = disc
        er = arb(0,rad)
        return mid+acb(er,er)

    def enclose(value):
        center = acb(value.real.mid(),value.imag.mid())
        return center,abs(value-center).upper()

    def affine(disc, factor, offset):
        center, rounding = enclose(factor*disc[0]+offset)
        return center,(rounding+abs(factor)*disc[1]).upper()

    def native_angle(y, want_slope=False, state=False):
        # Three images of the universal trapping disk sharpen the enclosure
        # of its unique periodic point for this small parameter box.
        parameter = unit*y
        disc = (acb(1),radius)
        for _ in range(3):
            center, rad, _, _ = advance(*disc,parameter,period)
            disc = (center,rad)
        basepoint=box(disc)
        coherent = acb(0)
        stages = []
        for _ in range(period):
            for sign in (-1,1):
                before = box(disc)
                coherent += sign*parameter*before
                disc = stage(*disc,sign*parameter)
                stages.append((sign,before,box(disc)))
        # Each pair of constant stage derivatives contributes y^2>0.
        mu = ((2*period)*y.log()+coherent).exp()
        angle = mu.arg()*180/arb.pi()
        if state:
            return angle,mu,basepoint
        if not want_slope:
            return angle, abs(mu)
        # Differentiate the full loop on its fixed point. First hold the
        # starting point fixed, then use (1-G_p) p' = G_y.
        slope = (acb(0),arb(0))
        for sign, before, after in stages:
            slope = affine(slope,sign*parameter*after,sign*unit*before*after)
        slope = enclose(box(slope)/(1-mu))
        log_slope = acb(2*period/y)
        for sign, before, after in stages:
            log_slope += sign*unit*before+sign*parameter*box(slope)
            slope = affine(slope,sign*parameter*after,sign*unit*before*after)
        return angle, abs(mu), log_slope.imag*180/arb.pi()

    boxes = {
        -30:"0.509892982814123928581849896272386908561243",
         30:"0.509892983131264277956320913142114370309900"
    }
    report = []
    for wanted, left in boxes.items():
        lo = Fraction(left)
        width = Fraction(1, 10**len(left.split(".")[1]))
        hi = lo+width
        ylo, yhi = rational(lo), rational(hi)
        z0, _ = native_angle(ylo)
        z1, _ = native_angle(yhi)
        ybox = ylo.union(yhi)
        zbox, mag, slope = native_angle(ybox,True)
        assert z0 < wanted < z1 and zbox.contains(wanted) and slope > 0, (z0-wanted,z1-wanted,zbox-wanted,slope)
        assert -90 < zbox < 90 and 0 < mag < 1
        report.append(dict(P_target_degrees=wanted, Q_target_degrees=-wanted,
                           height_lower=left,height_width=str(width),
                           P_minus_target_left=(z0-wanted).str(12),
                           P_minus_target_right=(z1-wanted).str(12),
                           P_angle_derivative_deg_per_y=slope.str(18),
                           multiplier_modulus=mag.str(15)))
    # Certify a *single* invertible branch from the recorded y0 through both
    # crossings. Subdivide exact rational endpoints and use their outward
    # rounded union as the argument of the full implicit derivative enclosure.
    begin, end = BRANCH_START, BRANCH_END
    pending=[(begin,end,0)]
    accepted=[]
    while pending:
        low,high,depth=pending.pop()
        angles,moduli,slopes=native_angle(rational(low).union(rational(high)),True)
        if slopes>rational("1.6e11") and slopes<rational("2.1e11") and angles> -140 and angles<40 and moduli>0:
            accepted.append((angles,moduli,slopes,depth))
        else:
            assert depth < 17, (low,high,angles,moduli,slopes)
            mid=(low+high)/2
            pending.extend([(low,mid,depth+1),(mid,high,depth+1)])
    angle0,_=native_angle(rational(begin))
    angle1,_=native_angle(rational(end))
    min_slope=min(a[2].lower() for a in accepted)
    max_slope=max(a[2].upper() for a in accepted)
    # The two independent inverse procedures can now use these coarse
    # integer bounds without reading a rounded decimal lower or upper bound.
    assert min_slope > SLOPE_MIN and max_slope < SLOPE_MAX
    inverse=dict(y_start="0.50989298230",y_end="0.50989298314",
                 angle_start_degrees=angle0.str(17),angle_end_degrees=angle1.str(17),
                 cells=len(accepted),maximum_depth=max(a[3] for a in accepted),
                 slope_lower_degrees_per_y=min_slope.str(15),
                 slope_upper_degrees_per_y=max_slope.str(15))
    report_dict=dict(bits=ctx.prec, centerline_uniform_height_interval=endpoints,
                scalar_period=period,ordered_period=2*period,
                cap_trap_radius="1e-15",uniform_image_radius=image.str(15),
                uniform_contraction=bound.str(15),
                proper_divisor_disjointness={str(k):v.str(12) for k,v in div_gap.items()},
                crossings=report,monotone_coordinate=inverse)

    return report_dict


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
