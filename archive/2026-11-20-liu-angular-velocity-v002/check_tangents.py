"""Move the angle, solve for the nearby zero and compare with the analytic tangent."""
import argparse
import json
from pathlib import Path

import mpmath
from mpmath import mp


def nearby_zero(angle, rho):
    shift = mp.mpf("0.5") - angle / mp.pi

    def hurwitz_sum(w):
        return mp.zeta(w, shift) + mp.zeta(w, 1 - shift)

    root = mp.findroot(hurwitz_sum, (rho, rho + mp.mpc("1e-6", "1e-6")))
    if abs(hurwitz_sum(root)) >= mp.mpf("1e-48") or abs(root-rho) >= mp.mpf("0.001"):
        raise ArithmeticError("The nearby zero failed the residual or distance check.")
    return root


def centered_difference(angle, rho, step):
    return (nearby_zero(angle + step, rho) - nearby_zero(angle - step, rho)) / (2 * step)


def check_zero(index):
    rho = mp.zetazero(index)
    quotient = mp.dirichlet(1 + rho, [0, 1, -1]) / (1 - 3**(-rho))
    positive_tangent = -3 * rho * quotient / (mp.pi * mp.zeta(rho, derivative=1))
    step = mp.mpf("1e-8")
    results = []
    for sign in (1, -1):
        angle = sign * mp.pi / 6
        full = centered_difference(angle, rho, step)
        half = centered_difference(angle, rho, step / 2)
        tangent = (4 * half - full) / 3
        error = abs(tangent - sign * positive_tangent)
        if error >= mp.mpf("1e-24"):
            raise ArithmeticError("The numerical tangent disagrees with the formula.")
        results.append({"angle_sign": sign, "real": mp.nstr(tangent.real, 25),
                        "imaginary": mp.nstr(tangent.imag, 25), "absolute_difference": mp.nstr(error, 9)})
    return {"zero_index": index, "tangents_per_radian": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    mp.dps = 62
    report = {"mpmath": mpmath.__version__, "decimal_working_precision": mp.dps,
              "central_difference_steps_radians": ["1e-8", "5e-9"],
              "checks": [check_zero(index) for index in (1, 6, 10)]}
    data = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8", newline="\n")
    else:
        print(data, end="")
