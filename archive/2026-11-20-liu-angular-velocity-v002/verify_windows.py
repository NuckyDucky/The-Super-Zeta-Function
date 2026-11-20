"""Count every zero across each height window and check its critical-line brackets."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq


ARCHIVE = Path(__file__).resolve().parents[1]
FIRST = ARCHIVE / "2026-11-17-dottie-grid-match-v001"
LATER = ARCHIVE / "2026-11-18-superzeta-distance-v001"


def rational(value):
    value = Fraction(value)
    return fmpq(value.numerator, value.denominator)


def dottie_height():
    eta = rational("4.749479070945369e-8")
    y = rational("0.509892982511772")
    return arb.pi() / (80 * arb((eta / y)**2).log1p())


def frozen_brackets(k):
    if k == 1:
        record = json.loads((FIRST / "dottie-grid-certificate.json").read_text())
        pairs = record["arms"]["dottie"]["broad"]["line_brackets"]
    else:
        record = json.loads((LATER / f"coverage-h{k}.json").read_text())
        pairs = [entry["offset"] for cell in record["cells"] for entry in cell["brackets"]]
    return sorted((Fraction(left), Fraction(right)) for left, right in pairs)


def count_at_guard(endpoint):
    guard = arb(0, arb(2)**-18)
    count = (endpoint + guard).zeta_nzeros().unique_fmpz()
    if count is None:
        raise ArithmeticError("The guarded endpoint did not give one integer zero count.")
    return int(count)


def hardy_sign(t):
    w = acb(arb(1) / 2, t)
    gamma = (w / 2).gamma()
    unit_factor = gamma / abs(gamma) * acb(0, -t * arb.pi().log() / 2).exp()
    z = unit_factor * w.zeta()
    if z.imag.contains(0):
        if z.real > 0:
            return 1
        if z.real < 0:
            return -1
    raise ArithmeticError("The real Hardy value did not give a certified sign.")


def verify_window(k, half_width):
    ctx.prec = 96
    center = k * dottie_height()
    lower = count_at_guard(center - arb(rational(half_width)))
    upper = count_at_guard(center + arb(rational(half_width)))

    ctx.prec = 144
    center = k * dottie_height()
    pairs = frozen_brackets(k)
    previous_right = -half_width
    checked = []
    for left, right in pairs:
        if not previous_right < left < right < half_width:
            raise ArithmeticError("The rational brackets must be disjoint and inside the window.")
        signs = [hardy_sign(center + arb(rational(x))) for x in (left, right)]
        if signs[0] * signs[1] != -1:
            raise ArithmeticError("The two Hardy signs do not bracket a zero.")
        checked.append({"offsets": [str(left), str(right)], "signs": signs})
        previous_right = right
    if upper - lower != len(checked):
        raise ArithmeticError("The critical-line brackets do not exhaust the total count.")
    return {"multiple_of_T_D": k, "half_width": str(half_width), "N_lower": lower,
            "N_upper": upper, "zero_count": upper - lower, "hardy_brackets": checked}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = {
        "python_flint": flint.__version__, "flint": flint.__FLINT_VERSION__,
        "count_precision_bits": 96, "guard_radius": "1/262144", "hardy_precision_bits": 144,
        "windows": [verify_window(k, width) for k, width in
                    ((1, Fraction(1, 4)), (2, Fraction(1, 2)), (3, Fraction(1, 2)))],
    }
    data = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8", newline="\n")
    else:
        print(data, end="")
