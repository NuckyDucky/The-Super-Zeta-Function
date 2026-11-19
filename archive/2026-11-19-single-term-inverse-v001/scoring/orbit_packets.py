"""Blind packets from the continued period-640 right orbit at the sixth-path crossing.

Python 3.12, python-flint 0.9.0. Pass the local Super Zeta git checkout as the
positional argument. One file holds only the two labeled trace channels per
observation. Calibration, provenance and the visit labels go in a separate file.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

from flint import arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    archive = args.repo.resolve() / "archive"
    oriented = archive / "2026-11-19-oriented-return-v001" / "computations"
    transport = archive / "2026-11-19-zero-transport-v001" / "Dottie-Off-Axis-Return"
    crossing = archive / "2026-11-19-sixth-passes-v001" / "compute" / "revisit.json"
    sys.path[:0] = [str(oriented), str(transport)]
    import flank_path as flank
    from orbit_crossing import advance, stage
    from quarter_probe import degree, encode
    from verify_dottie_horn_slice import trapping_data

    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    flank.advance, flank.stage, flank.degree = advance, stage, degree
    flank.trapping_data = trapping_data
    ctx.prec, ctx.cap = 448, 5
    lo, hi, calibration = flank.calibration(1)
    bounds = json.loads(crossing.read_text(encoding="utf-8"))["bounds"]
    truths = []
    packets = []
    for index in (2, 1):
        phase = 60 - arb(bounds[f"alpha{index}"])
        # Invert just the midpoint as a proposal. The inequalities at the two
        # enlarged rational endpoints below enclose the entire crossing target.
        a, b = flank.tinybracket(1, phase.mid(), lo, hi)
        margin = Fraction(1, 10**26)
        a -= margin
        b += margin
        assert flank.moment(1,a,a,False)["a"] < phase < flank.moment(1,b,b,False)["a"]
        orbit = flank.moment(1,a,b,False)
        mu = orbit["mu"]
        assert abs(mu) < 1 and abs(mu) > 0
        # encode evaluates the normalized signed determinants' Taylor
        # coefficients at the origin. The only input is the fresh multiplier.
        mplus, mminus = encode(mu/abs(mu))
        row = {"Mplus": mplus.str(12), "Mminus": mminus.str(12)}
        assert all(arb(row[key]).contains(value) for key,value in
                   (("Mplus",mplus),("Mminus",mminus)))
        packets.append(row)
        truths.append({
            "visit":index, "hidden_turn_degrees":bounds[f"alpha{index}"],
            "native_angle_target_degrees":phase.str(23),
            "native_angle_from_multiplier_degrees":orbit["a"].str(23),
            "ReL":str(flank.ETA), "ImL":flank.stamp((a,b)),
            "multiplier":mu.str(21), "abs_multiplier":abs(mu).str(21),
            "trapping_disk_contraction_upper":orbit["k"].upper().str(13),
            "maximal_proper_divisor_disjointness_lower":orbit["gap"].lower().str(13),
            "Mplus": mplus.str(20), "Mminus":mminus.str(20)
        })
    record = {
        "precision_bits":ctx.prec,
        "crossing_sha256":hashlib.sha256(crossing.read_bytes()).hexdigest(),
        "chart":"right flank, continuation of original cap-marked orbit; first scalar phase P",
        "calibration":calibration, "primitive_scalar_period":320, "primitive_ordered_period":640,
        "readouts_in_packet_order":truths
    }
    args.outdir.mkdir(exist_ok=True,parents=True)
    for name,data in (("packets",{"public_packets":packets}),("truth",record)):
        (args.outdir/f"{name}.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(truths,indent=2))


if __name__ == "__main__":
    main()
