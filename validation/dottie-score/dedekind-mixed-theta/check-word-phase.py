"""Compare the two corrected reference phases on the same Cayley circle."""

import importlib.util
import json
from pathlib import Path

from flint import acb, arb, ctx


def circle_replay():
    path = Path(__file__).with_name("check-completed-circle.py")
    spec = importlib.util.spec_from_file_location("completed_circle", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ctx.prec = 144
    ctx.threads = 1
    replay = circle_replay()
    center = acb(arb(3) / 4, replay.HEIGHT)
    radius = arb(31) / 128
    h, coefficients, _ = replay.zeta_polynomial(center, radius)
    eps = arb(0, arb(1) / 10**9)
    i = acb(0, 1)
    pi = arb.pi()
    log2, log3, logpi = arb(2).log(), arb(3).log(), pi.log()
    quarter_turns = (acb(1), i, acb(-1), -i)

    def readings(offset):
        w = center + offset
        zeta = replay.evaluate(coefficients, offset / h) + acb(eps, eps)
        one = (-logpi * w).exp() * ((log3 * w).exp() - 1) * zeta
        two = ((log2 * w).exp() - 1) * one
        return one, two

    # The integer rotations were selected from a preliminary phase scan.
    # The whole-circle checks below do not use that scan.
    specs = [(acb(-9067, 4217) / 10000, 9, 5), (acb(2436, 9699) / 10000, 4, 3)]
    reports = []
    for lap, (axis, imag_coefficient, real_coefficient) in enumerate(specs):
        pending = [(a, 4, j) for a in range(4) for j in range(16)]
        accepted = []
        lower = None
        while pending:
            quarter, depth, index = pending.pop()
            n = 2**depth
            t = arb(2 * index + 1) / (2 * n) + arb(0, arb(1) / (2 * n))
            offset = radius * quarter_turns[quarter] * (1 + i * t) / (1 - i * t)
            value = axis * readings(offset)[lap]
            margin = -imag_coefficient * value.imag - real_coefficient * abs(value.real)
            if margin > 0:
                bound = margin.lower()
                lower = bound if lower is None else min(lower, bound)
                accepted.append((quarter, depth, index))
            elif depth < 13:
                pending.extend(((quarter, depth + 1, 2 * index),
                                (quarter, depth + 1, 2 * index + 1)))
            else:
                raise ArithmeticError(f"Lap {lap + 1}, cell {quarter}:{index}/{n}: {margin}")

        depth = max(depth for _, depth, _ in accepted)
        coverage = [[0] * 2**depth for _ in quarter_turns]
        for quarter, cell_depth, index in accepted:
            width = 2 ** (depth - cell_depth)
            for point in range(index * width, (index + 1) * width):
                coverage[quarter][point] += 1
        assert all(count == 1 for quarter in coverage for count in quarter)
        reports.append({
            "laps": lap + 1,
            "coneRealToNegativeImaginaryRatio": f"{imag_coefficient}/{real_coefficient}",
            "acceptedClosedCells": len(accepted),
            "coveredUniformCells": 4 * 2**depth,
            "lowestConeMargin": lower.str(12),
        })

    # Two actual one-lap inputs witness a wider spread than the two-lap cone.
    one_lap = [readings(radius * (i * (2 * j * pi / 96)).exp())[0] for j in range(96)]
    witness = None
    for a, left in enumerate(one_lap):
        for b, right in enumerate(one_lap[a + 1:], a + 1):
            dot = left.real * right.real + left.imag * right.imag
            cosine = dot / (abs(left) * abs(right))
            if cosine < -arb(2) / 5:
                witness = {"inputsOver96Turns": [a, b], "cosineUpper": cosine.upper().str(12)}
                break
        if witness:
            break
    assert witness, "No pair certifies a wider one-lap spread."
    print(json.dumps({
        "ordinaryHeight": replay.HEIGHT,
        "radius": "31/128",
        "zetaErrorBudget": "1e-9",
        "wholeCircleCones": reports,
        "oneLapSpreadWitness": witness,
    }, indent=2))


if __name__ == "__main__":
    main()
