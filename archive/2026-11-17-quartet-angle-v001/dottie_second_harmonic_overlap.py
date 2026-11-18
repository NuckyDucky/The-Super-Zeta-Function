"""Test whether the archived line zeros recur at the same marked Dottie phase.

Before counting, save the two old offsets at the second harmonic as two
full-width boxes and the same broad window as the first-harmonic experiment.
Run 'freeze' and then 'count' with the original experiment's environment.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from dottie_grid_nomination import centers, fingerprint, write_new
from dottie_grid_trial import box, certify, ctx, OUTER, RIGHT


HERE = Path(__file__).resolve().parent
PARENT = HERE / "dottie-grid-certificate.json"
PLAN = HERE / "dottie-second-harmonic-plan.json"
RESULT = HERE / "dottie-second-harmonic-count.json"


def make_plan():
    cert = json.loads(PARENT.read_bytes())
    brackets = cert["arms"]["dottie"]["broad"]["line_brackets"]
    assert len(brackets) == 2
    return {
        "prediction": "Each certified first-harmonic zero repeats at its previous height plus T_D. Test each entire inherited offset interval at 2*T_D across the admissible real strip.",
        "parent_sha256": fingerprint(PARENT),
        "precision_bits": 192,
        "harmonic": 2,
        "boxes": {
            "broad": box(OUTER, (Fraction(-1, 4), Fraction(1, 4))),
            "signed_half": box(RIGHT, (Fraction(-1, 4), Fraction(1, 4))),
            "negative_sample": None,
            "positive": [
                {"parent_index": index, "box": box(OUTER, interval)}
                for index, interval in enumerate(brackets, 1)
            ],
        },
    }


def count():
    plan = json.loads(PLAN.read_bytes())
    assert plan == make_plan()
    ctx.prec = plan["precision_bits"]
    _, period, _, _ = centers()
    height = plan["harmonic"] * period
    report = {
        "plan_sha256": fingerprint(PLAN),
        "height": height.str(45),
        "count": certify(height, plan["boxes"]),
    }
    write_new(RESULT, report)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("freeze", "count"))
    if parser.parse_args().mode == "freeze":
        write_new(PLAN, make_plan())
        print(fingerprint(PLAN))
    else:
        count()
