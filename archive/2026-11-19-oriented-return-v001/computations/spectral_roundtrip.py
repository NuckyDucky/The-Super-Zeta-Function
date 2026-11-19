"""Recover the centerline cap witness from signed twisted characteristic roots.

Run with Python 3.12, python-flint 0.9.0 and mpmath 1.3.0. The branch
certificate is regenerated from the archived exponential stages on every run.
"""
import argparse
import json
from pathlib import Path

import mpmath as mp
from flint import acb, arb, ctx


from orbit_crossing import BRANCH_START, BRANCH_END, SLOPE_MIN, SLOPE_MAX, advance, rational, stage, verify


def enclose_root(mark, sign):
    # A=e^(i theta)=e^(-i phi). The solver only proposes a disk center.
    c, h = mark.real, -mark.imag
    real = lambda t: mp.mpf(t.mid().str(100, radius=False))
    cz, hz = real(c), real(h)
    seed = (7+2j, 8+3j) if sign == 1 else (4+2j, 5+3j)
    candidate = mp.findroot(lambda z: z-sign*(cz*mp.cos(z)+hz*mp.sin(z)), seed)
    u = acb(arb(mp.nstr(candidate.real, 96)).mid(), arb(mp.nstr(candidate.imag, 96)).mid())
    f = u-sign*(c*u.cos()+h*u.sin())
    df = 1+sign*(c*u.sin()-h*u.cos())
    for exponent in (80, 70, 60, 50, 40, 36, 32, 28, 24, 20, 16, 12):
        rad = rational(f"1e-{exponent}")
        # |f''(u)| = |cos(u-phi)| <= cosh(|Im u|) for real phi.
        if abs(f)+(abs(u.imag)+rad).cosh()*rad**2/2 < abs(df)*rad:
            err = arb(0, rad.upper())
            assert u.imag > rad
            return u+acb(err, err)
    raise ArithmeticError("Failed to isolate a nonreal characteristic root")


def emit(mark):
    return tuple(enclose_root(mark, sign) for sign in (1,-1))


def decode(roots):
    # Only two spectral root boxes in known stage order enter this function.
    directions = []
    for sign, root in zip((1,-1), roots, strict=True):
        x, y = root.real, root.imag
        directions.append(sign*acb(0,-x).exp()*acb(x/y.cosh(), -y/y.sinh()))
    p, q = directions
    assert p.overlaps(q)
    return acb(p.real.intersection(q.real), p.imag.intersection(q.imag))


def run():
    # Regenerate the trapping, period and branch derivative bounds used below.
    calibration = verify()
    branch = calibration["monotone_coordinate"]
    mp.mp.dps = 105
    I = acb(0, 1)
    domain = rational(branch["y_start"]).union(rational(branch["y_end"]))
    slopes = arb(SLOPE_MIN).union(arb(SLOPE_MAX))

    def native(y):
        L = I*y
        disc = (acb(1), rational("1e-15"))
        for _ in range(4):
            center, radius, _, _ = advance(*disc, L, 320)
            disc = center, radius
        def point():
            err = arb(0, disc[1])
            return disc[0]+acb(err,err)
        p = point()
        lifted = acb(640*y.log())
        for _ in range(320):
            for rate in (-L,L):
                lifted += rate*point()
                disc = stage(*disc,rate)
        # On the centerline the second complete return is its conjugate.
        return (I*lifted.imag).exp(), p

    def degrees(unit):
        return unit.arg()*180/arb.pi()

    def locate(unit):
        target = degrees(unit)
        assert arb(branch["angle_start_degrees"]) < target < arb(branch["angle_end_degrees"])
        interval = domain
        for _ in range(100):
            mid = interval.mid()
            assert rational(BRANCH_START) < mid < rational(BRANCH_END)
            theta = degrees(native(mid)[0])
            new = interval.intersection(mid+(target-theta)/slopes)
            if new.rad() < rational("1e-48") or new.rad() > interval.rad()*rational("0.95"):
                return new
            interval = new
        raise ArithmeticError("Branch inversion failed to contract")

    def packet_report(roots):
        return [dict(stage=s, real=u.real.str(90), imag=u.imag.str(90))
                for s, u in zip(("+","-"), roots, strict=True)]

    original = rational("0.509892982511772")
    step = acb(arb(3).sqrt()/2, arb(1)/2)
    source_mark, original_p = native(original)
    packet0 = emit(source_mark)
    recovered0 = decode(packet0)
    assert recovered0.overlaps(source_mark)
    encoded0 = locate(recovered0)
    assert encoded0.contains(original)
    before = locate(recovered0*step.conjugate())
    # A fresh complete lap at the new parameter supplies the second spectrum.
    before_mark, _ = native(before)
    packet1 = emit(before_mark)
    recovered1 = decode(packet1)
    restored = locate(recovered1*step)
    assert restored.contains(original) and 2*restored.rad() < rational("1.44e-45")
    restored_p = native(restored)[1]
    assert restored_p.overlaps(original_p)
    pivot_roots = emit(-I)
    assert decode(pivot_roots).contains(-I)

    def alias(mark, direct_parameter):
        flipped = -mark.conjugate()
        other = locate(flipped)
        assert not other.overlaps(direct_parameter)
        return dict(angle_degrees=degrees(flipped).str(35), y=other.str(65))
    return dict(precision_bits=ctx.prec, scalar_period=320, ordered_period=640,
                calibrated_height=branch, source_y=original.str(65),
                source_angle=degrees(recovered0).str(44), original_roots=packet_report(packet0),
                recovered_direct_y=encoded0.str(65),
                rotated_y=before.str(65), rotated_angle=degrees(recovered1).str(44),
                rotated_roots=packet_report(packet1),
                returned_y=restored.str(65), width_upper=(2*restored.rad()).upper().str(12),
                exact_source_inside_return=restored.contains(original),
                returned_cap_P=restored_p.str(60), returned_cap_Q=restored_p.conjugate().str(60),
                alias_of_source_for_squared_data=alias(recovered0,original),
                alias_of_turned_for_squared_data=alias(recovered1,before),
                pivot_roots=packet_report(pivot_roots),
                phase_at_pivot=decode(pivot_roots).str(40))


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    record = json.dumps(run(), indent=2)
    if args.output:
        args.output.write_text(record+"\n", encoding="utf-8")
    else:
        print(record)
