"""Replay the archived Hurwitz and two-input reports with their pinned arithmetic runtime."""

from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
import json
from pathlib import Path
import platform
import subprocess
import sys
from tempfile import TemporaryDirectory


ARCHIVE = Path(__file__).resolve().parents[1] / "archive" / "2026-11-20-hurwitz-speed-mean-square-v001"
REPORTS = (
    ("verify_moments.py", "windows-and-means.json"),
    ("verify_two_inputs.py", "two-inputs.json"),
)


def outward_decimal_bounds(lower, upper, digits):
    """Round the positive report endpoints down and up to significant decimal digits."""
    lower, upper = Decimal(lower), Decimal(upper)
    with localcontext() as context:
        context.prec = digits + 1  # An endpoint can carry into the next decade.
        lower_unit = Decimal(1).scaleb(lower.adjusted() + 1 - digits)
        upper_unit = Decimal(1).scaleb(upper.adjusted() + 1 - digits)
        return (
            str(lower.quantize(lower_unit, rounding=ROUND_FLOOR)),
            str(upper.quantize(upper_unit, rounding=ROUND_CEILING)),
        )


def check_recovery_precision():
    from flint import arb, ctx

    sys.path.insert(0, str(ARCHIVE))
    sys.dont_write_bytecode = True
    from verify_two_inputs import recover_from_five

    report = json.loads((ARCHIVE / "two-inputs.json").read_bytes())
    stored = report["inverse_from_five_real_values"]["full_readings_including_the_real_root"]
    ctx.prec = 320
    widths = {}
    print("Five archived readings rounded outward by significant digits, using 320-bit Arb:")
    for digits in (42, 43, 51, 52):
        rounded = [outward_decimal_bounds(lo, hi, digits) for lo, hi in stored]
        readings = [arb(lo).union(arb(hi)) for lo, hi in rounded]
        try:
            radius, angle = recover_from_five(readings)
        except ArithmeticError as error:
            if digits != 42 or str(error) != "The five readings did not resolve the first pair.":
                raise
            print("  42 digits: first pair unresolved")
            continue

        if digits == 42:
            raise ArithmeticError("Expected the first pair to remain unresolved at 42 digits.")
        if not radius.is_finite() or not angle.is_finite():
            raise ArithmeticError(f"Expected finite recovery at {digits} digits.")

        radius_width, angle_width = 2 * radius.rad(), 2 * angle.rad()
        widths[digits] = radius_width, angle_width
        print(f"  {digits} digits: radius width {radius_width.str(8)}, "
              f"angle width {angle_width.str(8)} radians")

    radius_width_43, _ = widths[43]
    if not (arb("0.78") < radius_width_43 < arb("0.82")):
        raise ArithmeticError("Expected the radius width at 43 digits to be about 0.80.")
    target = arb("1e-9")
    if not (widths[51][0] > target and widths[51][1] < target):
        raise ArithmeticError("Expected the radius width above 1e-9 and the angle width below it at 51 digits.")
    if not all(width < target for width in widths[52]):
        raise ArithmeticError("Expected both widths below 1e-9 at 52 digits.")


def main():
    import flint

    versions = platform.python_version(), flint.__version__, flint.__FLINT_VERSION__
    expected_versions = "3.12.11", "0.9.0", "3.6.0"
    if versions != expected_versions:
        raise SystemExit(f"Expected Python, python-flint, and FLINT {expected_versions}. Got {versions}.")

    with TemporaryDirectory(prefix="super-zeta-replay-") as temporary:
        scratch = Path(temporary)
        for script, report in REPORTS:
            generated = scratch / report
            print(f"Replaying {script}...", flush=True)
            subprocess.run(
                [sys.executable, "-B", str(ARCHIVE / script), "--output", str(generated)],
                cwd=scratch,
                check=True,
            )
            if generated.read_bytes() != (ARCHIVE / report).read_bytes():
                raise SystemExit(f"{report} differs from the archived report.")
            print(f"  {report} matches byte for byte", flush=True)

    check_recovery_precision()


if __name__ == "__main__":
    main()
