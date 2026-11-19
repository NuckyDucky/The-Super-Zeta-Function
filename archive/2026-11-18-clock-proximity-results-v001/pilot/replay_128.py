"""Replay the two previously published pilot pairs, consulting results only at the end."""
import hashlib
import json
import platform
import re
from fractions import Fraction
from pathlib import Path
from time import perf_counter

import flint
from flint import acb, arb, ctx, fmpq


def rational(value):
    x = Fraction(value)
    return fmpq(x.numerator, x.denominator)


def certify_center(height):
    count = height.zeta_nzeros().unique_fmpz()
    assert count is not None
    roots = acb.zeta_zeros(count, 2)
    assert all(z.real == arb(1) / 2 for z in roots)
    lower, upper = [z.imag for z in roots]
    assert lower < height < upper
    left, right = height - lower, upper - height
    if left < right:
        side, nearest = "lower", left
    elif right < left:
        side, nearest = "upper", right
    else:
        raise ArithmeticError("Unresolved nearest ordinate")
    assert nearest < arb(1) / 4
    return {"N": int(count), "center": height, "lower": lower, "upper": upper,
            "distance": nearest, "closest": side}


if __name__ == "__main__":
    ctx.prec = 128
    ctx.threads = 1
    start = perf_counter()
    directory = Path(__file__).resolve().parent
    protocol = (directory / "protocol.json").read_bytes()
    digest = hashlib.sha256(protocol).hexdigest()
    assert digest == "3f51d2bf0ed501d1f1dfba019f534102a22bc8e52e77009fc42b3e494ccd32ff"
    cases = []
    for arm in json.loads(protocol)["arms"]:
        ratio_sq = (rational(arm["x"]) / rational(arm["y"])) ** 2
        dottie = arb.pi() / (80 * arb(ratio_sq).log1p())
        grid = int(arm["n"]) * arb.pi()
        case = {}
        for label, height in (("Dottie", dottie), ("grid", grid)):
            tick = perf_counter()
            result = certify_center(height)
            print(label, result["N"], result["distance"], flush=True)
            result["seconds"] = round(perf_counter() - tick, 3)
            case[label] = result
        if case["grid"]["distance"] < case["Dottie"]["distance"]:
            case["closer"] = "grid"
        elif case["Dottie"]["distance"] < case["grid"]["distance"]:
            case["closer"] = "Dottie"
        else:
            raise ArithmeticError("Unresolved comparison")
        cases.append(case)

    prior = json.loads((directory / "results.json").read_bytes())
    assert prior["protocol_sha256"] == digest
    for case, old_case in zip(cases, prior["pairs"], strict=True):
        assert case["closer"] == old_case["closer"]
        for channel in ("Dottie", "grid"):
            row, old = case[channel], old_case[channel]
            assert row["closest"] == old["closest"] and row["N"] == old["N"]
            assert old["indices"] == [row["N"], row["N"] + 1]
            archived = {key: arb(old[key]) for key in ("center", "distance")}
            for side, display in zip(("lower", "upper"), old["adjacent_zeros"], strict=True):
                m = re.fullmatch(r"(0\.50*) \+ (\[.*?\])j", display)
                assert m is not None and arb(m[1]) == arb(1) / 2
                archived[side] = arb(m[2])
            row["overlap_96"] = {key: row[key].overlaps(value) for key, value in archived.items()}
            assert all(row["overlap_96"].values())
            for key in archived:
                row[key] = row[key].str(38)
    payload = dict(bits=128, threads=1, protocol_sha256=digest, python=platform.python_version(),
                   python_flint=flint.__version__, flint=flint.__FLINT_VERSION__,
                   seconds=round(perf_counter() - start, 3), pairs=cases)
    with (directory / "replay_128.json").open("w", encoding="utf-8") as file:
        json.dump(payload, file, indent=2)
        file.write("\n")
    print(json.dumps(payload, indent=2))
