"""Replay the archived period-320 cap over the flanks used by the height theorem."""

import argparse
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx, __version__ as flint_version


ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "archive" / "2026-11-17-quartet-return-recursion-v001" / "computations"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--computations-dir", type=Path, default=ARCHIVE)
    args = parser.parse_args()
    sys.path.insert(0, str(args.computations_dir.resolve()))
    import verify_dottie_horn_slice as orbit

    ctx.prec = 384
    x, y = arb(orbit.OFFSET), arb(orbit.HEIGHT)
    width = arb("1e-12")
    reach = arb(10**8)
    assert orbit.PERIOD == 320

    def height(offset):
        return 4 * arb.pi() / (orbit.PERIOD * ((offset/y)**2).log1p())

    center = height(x)
    lo_offset = height(x + width) - center
    hi_offset = height(x - width) - center
    assert lo_offset < -reach and hi_offset > reach

    inverse_witnesses = []
    for shift in (-reach, arb(0), reach):
        target = center + shift
        offset = y * (4 * arb.pi() / (orbit.PERIOD * target)).expm1().sqrt()
        assert abs(offset - x) < width
        assert (height(offset) - target).contains(0)
        inverse_witnesses.append({"shift": shift.str(20), "flank": offset.str(31)})

    orbit.DISK_RADIUS = arb("1e-5").upper()
    parameter_uncertainty = arb(0, width.upper())
    phases = []
    for flank in (-1, 1):
        parameter = acb(flank * (x + parameter_uncertainty), y)
        for phase, rate in (("P", parameter), ("Q", -parameter)):
            root, entry, residual, derivative_bound = orbit.trapping_data(rate)
            radius = (residual / (1 - derivative_bound)).upper()
            lifted = orbit.PERIOD * (rate.log() + (-rate).log())
            for _ in range(orbit.PERIOD):
                for arrow in (-rate, rate):
                    error = arb(0, radius)
                    lifted += arrow * (root + acb(error, error))
                    root, radius = orbit.stage(root, radius, arrow)
            winding = -flank
            shifted_argument = lifted.imag - 2 * arb.pi() * winding
            assert -arb.pi() < shifted_argument < arb.pi()
            assert abs(lifted.exp()) < 1
            measured = ((lifted.imag - lifted.exp().arg()) / (2*arb.pi())).unique_fmpz()
            assert measured == winding
            phases.append({
                "flank": flank,
                "phase": phase,
                "capture_error": entry.str(16),
                "return_residual": residual.str(16),
                "derivative_upper": derivative_bound.str(18),
                "shifted_argument": shifted_argument.str(20),
                "winding": winding,
            })

    print(json.dumps({
        "python_flint": flint_version,
        "precision_bits": ctx.prec,
        "flank_x": orbit.OFFSET,
        "midpoint_y": orbit.HEIGHT,
        "flank_half_width": "1e-12",
        "trapping_radius": "1e-5",
        "cap": 1,
        "cap_cycles": orbit.BLOCKS,
        "scalar_period": orbit.PERIOD,
        "ordered_period": 2 * orbit.PERIOD,
        "height_center": center.str(43),
        "height_endpoint_offsets": [lo_offset.str(23), hi_offset.str(23)],
        "witnesses_by_height": inverse_witnesses,
        "flank_phases": phases,
    }, indent=2))


if __name__ == "__main__":
    main()
