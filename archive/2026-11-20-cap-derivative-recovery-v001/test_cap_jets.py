"""Blind cap-jet test. Python 3.12, python-flint 0.9.0. Run the three actions in order."""
import argparse
import hashlib
import json
import secrets
from fractions import Fraction
from itertools import combinations
from pathlib import Path

from flint import acb, acb_series, arb, ctx

ctx.prec = 192
WORDS = ("++--", "+--+", "--++", "-++-", "+-+-", "-+-+")
PI = arb.pi()
L = acb(0, PI)
H = arb(2) ** -24
R = arb(2) ** -10
REMAINDER = (H/R)**3 / (4*(1-H/R))
CHANNELS = ("value", "slope", "second", "nudge")


def encode(z):
    return [str(z.real), str(z.imag)]


def unpack(bounds):
    return acb(arb(bounds[0]), arb(bounds[1]))


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def execute(word, z):
    for letter in word:
        z = (z*(L if letter == "+" else -L)).exp()
    return z


def direct_readings(word):
    polynomial = execute(word, acb_series([1, 1], prec=3))
    return dict(zip(CHANNELS, map(encode, (
        polynomial[0], polynomial[1], 2*polynomial[2], execute(word, acb(1+H))
    ))))


def prediction(word):
    prefix, total = acb(1), acb(0)
    for letter in word:
        prefix *= -L if letter == "+" else L
        total += prefix
    second = -prefix*total
    return {"value": acb(-1), "slope": prefix, "second": second,
            "nudge": -1 + H*prefix + H**2*second/2}


def log_detector_at_two(exponent):
    # Coefficient of -D7'/(7 D7) at 2^exponent divided by log 2.
    return 1 + Fraction((-1)**exponent, 7)


def from_detector(word):
    exponent = 0
    normalized = acb(0)
    exponents, weights = [], []
    for j, letter in enumerate(word, 1):
        exponent += 1 if letter == "-" else 2
        weight = log_detector_at_two(exponent)
        prefix_sign = 7*(weight-1)
        assert prefix_sign.denominator == 1
        normalized -= int(prefix_sign)*(-L)**j
        exponents.append(exponent)
        weights.append(str(weight))
    return normalized, exponents, weights


def commitment(key):
    return hashlib.sha256(json.dumps(key, sort_keys=True).encode()).hexdigest()


def prepare(directory):
    directory.mkdir(parents=True, exist_ok=True)
    if any((directory / name).exists() for name in ("packets.json", "calls.json", "reveal.json")):
        raise FileExistsError("Choose an empty directory for a fresh trial")
    order = list(WORDS)
    secrets.SystemRandom().shuffle(order)
    labels = dict(zip("ABCDEF", order))
    key = {"labels": labels, "nonce": secrets.token_hex(16)}
    write(directory/"packets.json", {"commitment": commitment(key),
          "cases": {tag: direct_readings(word) for tag, word in labels.items()}})
    write(directory/"reveal.json", key)


def decode(packets):
    models = {word: prediction(word) for word in WORDS}
    calls = {}
    for tag, sample in packets["cases"].items():
        matches = {}
        for channel in CHANNELS:
            observed = unpack(sample[channel])
            if channel == "nudge":
                matches[channel] = [w for w, model in models.items()
                     if not abs(observed-model[channel]) > REMAINDER]
            else:
                matches[channel] = [w for w, model in models.items() if observed.overlaps(model[channel])]
        calls[tag] = matches
    return calls


def verify(directory):
    packets = read(directory/"packets.json")
    calls = read(directory/"calls.json")
    key = read(directory/"reveal.json")
    assert commitment(key) == packets["commitment"]
    assert set(key["labels"]) == set(packets["cases"]) == set("ABCDEF")
    assert sorted(key["labels"].values()) == sorted(WORDS)
    assert calls == decode(packets)
    assert PI < arb(16)/5
    models = {w: prediction(w) for w in WORDS}
    pair_gaps = [(a, b, abs(models[a]["nudge"]-models[b]["nudge"])) for a,b in combinations(WORDS,2)]
    assert all(2*REMAINDER < gap for _,_,gap in pair_gaps)
    assert REMAINDER < arb("5.69e-14") and PI**5*H**2-2*REMAINDER > arb("9.7e-13")
    weight_rows = {}
    for tag, word in key["labels"].items():
        for channel in ("value", "slope"):
            assert calls[tag][channel] == list(WORDS)
        for channel in ("second", "nudge"):
            assert calls[tag][channel] == [word]
        fresh = direct_readings(word)
        assert all(unpack(fresh[c]).overlaps(unpack(packets["cases"][tag][c])) for c in CHANNELS)
        observed = unpack(fresh["second"])/unpack(fresh["slope"])
        weighted, exponents, weights = from_detector(word)
        assert weighted.overlaps(observed)
        assert abs(unpack(fresh["nudge"])-models[word]["nudge"]) < REMAINDER
        weight_rows[word] = {"dyadic_exponents": exponents, "normalized_detector": weights}
    # The normalized Gaussian comparison product H^7 W has prime-ideal
    # coefficients 1+eta/7 times the angular phase (after dividing by log p).
    a, b = 3, 8
    sine = Fraction(4*a*b*(a*a-b*b), 73**2)
    gaussian_shell = (1-Fraction(1,7))*sine + (1+Fraction(1,7))*(-sine)
    assert gaussian_shell == Fraction(10560, 7*5329)
    return {"bits": ctx.prec, "h": "2^-24", "annotation": "Six samples, finite known family",
        "compatible_word_counts_per_case": {"value": 6, "first_derivative": 6, "second_derivative": 1,
             "single_nudged_value": 1},
        "labels_after_reveal": key["labels"], "dyadic_reconstruction": weight_rows,
        "normalized_gaussian_shell_imag_at_73": str(gaussian_shell),
        "taylor_remainder_upper": str(REMAINDER.upper()),
        "min_pair_exact_quadratic_centers_gap": str(PI**5*H**2),
        "true_nudge_pair_distance_lower": str((PI**5*H**2-2*REMAINDER).lower())}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare","decode","verify"])
    parser.add_argument("--folder", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Enable Python assertions.")
    if args.action == "prepare":
        prepare(args.folder)
    elif args.action == "decode":
        write(args.folder/"calls.json", decode(read(args.folder/"packets.json")))
    else:
        result = verify(args.folder)
        write(args.folder/"results.json", result)
        print(json.dumps(result, indent=2))
