"""Test the direction and the size of 192 measured Gaussian norm blocks."""
import gzip
import json
import sys
from pathlib import Path

from flint import acb, arb

PHASES = Path(__file__).resolve().parent.parent / "2026-11-20-gaussian-circle-phases-v001"
sys.path.insert(0, str(PHASES))
import replay as phase


def completed(cutoff, record):
    if not record["divided_by_factorial"]:
        raise ValueError("Expected factorial-normalized Taylor coefficients")
    mass = arb(record["mass"])
    coefficients = [acb(arb(x), arb(y)) for x, y in record["moments"]]

    def evaluate(angle):
        model = phase.arc
        model.N, model.mass = cutoff, mass
        model.coeff_taylor, model.order = coefficients, len(coefficients) - 1
        z = phase.coords(angle, False)
        return model.partial(arb(1) / 2 + z.real, z.imag)

    return evaluate


def positive_on_arc(margin, start, end, depth=0):
    if margin(start.union(end)) > 0:
        return
    if depth >= 16:
        raise ArithmeticError(f"Strict positivity unresolved on [{start}, {end}]")
    middle = (start + end) / 2
    positive_on_arc(margin, start, middle, depth + 1)
    positive_on_arc(margin, middle, end, depth + 1)


def classify(before, after, points_before, points_after, grid, margin):
    # One negative point disproves the strict test. A pass covers the continuous circle.
    for left, right in zip(points_before, points_after):
        if margin(left, right) < 0:
            return False
    for start, end in zip(grid, grid[1:]):
        positive_on_arc(lambda angle: margin(before(angle), after(angle)), start, end)
    return True


def projection(left, right):
    return (right * left.conjugate()).real


def size(left, right):
    return abs(left) - abs(right - left)


def check_example(before, after, grid):
    for start, end in zip(grid, grid[1:]):
        positive_on_arc(lambda angle: (after(angle) / before(angle)).real - arb("0.29"),
                        start, end)
    ratio = after(grid[139]) / before(grid[139])
    if not (arb("0.64400") < ratio.real < arb("0.64402")
            and arb("-1.05802") < ratio.imag < arb("-1.05799")
            and arb("1.11628") < abs(ratio - 1) < arb("1.11630")):
        raise ArithmeticError("Example enclosures did not reproduce")
    print("At 139*pi/128 the relative increment has size", abs(ratio - 1))
    print("On the whole circle for that block, Re(F_M/F_N) > 0.29")


def main():
    with gzip.open(PHASES / "moments.json.gz", "rt") as stream:
        records = json.load(stream)["cutoffs"]
    cutoffs = list(range(2**26, 2**28 + 1, 2**20))
    if sorted(map(int, records)) != cutoffs:
        raise ValueError("Unexpected norm cutoffs")
    grid = [phase.TAU * j / 256 for j in range(257)]
    before = completed(cutoffs[0], records[str(cutoffs[0])])
    points_before = [before(angle) for angle in grid[:-1]]
    counts = {(True, True): 0, (True, False): 0, (False, False): 0}
    examples = {}
    for cutoff in cutoffs[1:]:
        after = completed(cutoff, records[str(cutoff)])
        points_after = [after(angle) for angle in grid[:-1]]
        result = tuple(classify(before, after, points_before, points_after, grid, test)
                       for test in (projection, size))
        counts[result] += 1
        examples.setdefault(result, cutoff)
        if cutoff == 70254592:
            check_example(before, after, grid)
        before, points_before = after, points_after

    lower, upper = arb("6.3e-30"), arb("6.5e-30")
    for start, end in zip(grid, grid[1:]):
        positive_on_arc(lambda angle: abs(before(angle)) - lower, start, end)
    if not any(abs(value) < upper for value in points_before):
        raise ArithmeticError("Upper bound for boundary minimum unresolved")
    expected = {(True, True): 137, (True, False): 29, (False, False): 26}
    if counts != expected:
        raise ArithmeticError(f"Block classification changed: {counts}")
    print("Whole right circle, direction and size tests:")
    for pair, count in counts.items():
        print(f"direction={pair[0]}, size={pair[1]}: {count}; first ending cutoff {examples.get(pair)}")
    print("At the last cutoff: 6.3e-30 < min |F_N| < 6.5e-30")


if __name__ == "__main__":
    main()
