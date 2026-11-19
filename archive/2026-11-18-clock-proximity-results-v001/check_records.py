"""Recompute the published votes from the archived zero brackets, without a zero search."""

import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
PLAN = HERE.parent / "2026-11-18-clock-local-controls-protocol-v001"
ctx.prec = 256


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def distance_at(location, planned_height):
    center = arb(location["center"])
    assert center.overlaps(arb(planned_height))
    # FLINT printed each of these on-line zeros as "0.500... + [interval]j".
    bounds = []
    for entry in location["adjacent_zeros"]:
        real, imaginary = entry.removesuffix("j").split(" + ")
        assert arb(real) == arb(1) / 2
        bounds.append(arb(imaginary))
    assert bounds[0] < center < bounds[1]
    options = {"lower": center - bounds[0], "upper": bounds[1] - center,
               "censored": arb(1) / 4}
    selected = options.pop(location["status"])
    assert all(selected < other for other in options.values())
    assert selected.overlaps(arb(location["distance"]))
    return selected


def main():
    plan = read(PLAN / "protocol.json")
    orbits = read(HERE / "orbits.json")
    results = read(HERE / "results.json")
    assert results["protocol"] == orbits["protocol"] == digest(PLAN / "protocol.json")
    assert plan["evaluator_sha256"] == digest(PLAN / "local_controls.py")
    assert results["orbits_sha256"] == digest(HERE / "orbits.json")
    witnesses, orbit_rows, rows = plan["witnesses"], orbits["rows"], results["rows"]
    assert len(witnesses) == len(orbit_rows) == len(rows) == 32
    tally = Counter()
    for index, (nomination, orbit, row) in enumerate(zip(witnesses, orbit_rows, rows), 1):
        assert nomination["j"] == orbit["j"] == row["j"] == index
        assert nomination["x"] == orbit["x"] and orbit["status"] == row["orbit_status"]
        if orbit["status"] == "certified":
            assert {(m["side"], m["phase"]) for m in orbit["marks"] if abs(m["k"]) == 1} == {
                (side, phase) for side in (-1, 0, 1) for phase in ("P", "Q")}
            positions = ("left", "clock", "right")
            locations = row["locations"]
            left, clock, right = [
                distance_at(locations[name], height)
                for name, height in zip(positions, nomination["centers_left_clock_right"])]
            votes = []
            for other in (left, right):
                if clock < other:
                    votes.append("win")
                elif clock > other:
                    votes.append("loss")
                elif clock == other:
                    votes.append("tie")
                else:
                    votes.append("unresolved")
        else:
            assert "locations" not in row
            votes = ["unresolved", "unresolved"]
        assert row["votes"] == votes
        tally.update(votes)
    assert dict(tally) == results["totals"] and sum(tally.values()) == 64
    credit = tally["win"] + Fraction(tally["tie"], 2)
    interval = [str(credit / 64), str((credit + tally["unresolved"]) / 64)]
    assert interval == results["score_interval"]
    print(dict(tally), interval)


if __name__ == "__main__":
    main()
