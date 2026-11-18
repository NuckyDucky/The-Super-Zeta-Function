"""Freeze a height from the finite Dottie witnesses, before any spectral calculation."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from dottie_multiplier_winding import return_scale
from verify_dottie_horn_slice import HEIGHT, OFFSET, PERIOD, acb, arb, ctx


def write_new(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(data, indent=2, ensure_ascii=True) + "\n")


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rat(q):
    v = Fraction(q)
    return arb(v.numerator) / v.denominator


def centers():
    x, y = rat(OFFSET), rat(HEIGHT)
    d = PERIOD * ((x/y)**2).log1p()/2
    T = 2*arb.pi()/d
    n = ((T/arb.pi()+rat("1/2")).floor()).unique_fmpz()
    assert n is not None
    return d,T,int(n),n*arb.pi()


def nomination():
    ctx.prec = 384
    d,T,n,grid = centers()
    marks = []
    for vertical in (1,-1):
        for side in (-1,0,1):
            L = acb(side*rat(OFFSET), vertical*rat(HEIGHT))
            for origin,rate in (("P",L),("Q",-L)):
                scale,k,_ = return_scale(rate)
                assert abs(k) == 1
                marks.append({"vertical":vertical,"side":side,"origin":origin,
                              "minus_log_abs_multiplier":scale.str(25),"winding":k})
    assert abs(T-grid)>rat("1/2") and abs(T-grid)<arb.pi()/2
    return {
        "source_exact_decimals":{"x":OFFSET,"y":HEIGHT,"cap":"1"},
        "scalar_period":PERIOD,"ordered_stage_count":2*PERIOD,"orbit_bits":384,
        "rule":"Take the derivative of each lifted stage log(E_r(z))=r*z. Multiply its modulus over the m=320 occurrences of one arrow. Compare each flank with the midpoint by d=m*log(|x+i*y|/y). Positive H=2*pi*abs(k)/d, winding k from the coherent full scalar-return derivative log. Four flank addresses collapse by symmetry. Chosen external Mellin scale Z=ratio of these marked products (power c=1).",
        "log_scale_increment":d.str(38),"marks":marks,
        "arms":{"dottie":{"exact":"2*pi*abs(k)/(160*log1p((x/y)^2))","center":T.str(42)},
                "grid":{"n":n,"exact":"pi*n, nearest lattice point to the Dottie height","center":grid.str(42)}},
        "center_difference":(T-grid).str(32),
        "budget":{"positive_windows_per_arm":1,"height_offsets":["-1/4","1/4"],
                  "broad_beta":["1/16","15/16"],"signed_half_beta":["5/8","7/8"],
                  "predictor":"one degree-48 continued dyadic cosine/Riemann-Siegel phase polynomial per arm; find all complex polynomial roots in the open window; no zeta evaluations",
                  "certificate":"two mirrored-height-offset charts per arm (centers H +/- 1/8), 144 complex ball samples per chart at 192 bits; contour-depth cap 23, 64 Hardy sign cells per chart with up to 19 bisections. Unresolved remains unresolved.",
                  "tests":"both full rectangles and both signed-half slabs; every positive forecast gets its own disjoint-from-line box; preselect closest adjacent negative predicted pair per arm if present, padded 1/100 at each end, clipped to window. Check its wide count and line brackets.",
                  "positive_replication":"Any strictly off-line positive candidate count requires a second rigorous evaluation independent of the original interpolant before claiming a discovery; retain all four reflected/conjugate boxes and report any unresolved duplication.",
                  "primary_outcome":"number of certified off-line hit windows per arm (one each). Secondary: forecast vs actual broad counts; closer line gaps and simple line-zero counts do not count as off-line hits."}}


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("output",type=Path)
    path=p.parse_args().output
    result=nomination()
    write_new(path,result)
    print(result["arms"], result["center_difference"], fingerprint(path),flush=True)
