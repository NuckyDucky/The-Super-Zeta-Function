"""Blind recovery of signed exponential stages. Requires python-flint==0.9.0."""

import argparse
import hashlib
import itertools
import json
import secrets
from collections import Counter
from pathlib import Path

import flint
from flint import acb, acb_series, arb, ctx


ctx.prec = 192
ctx.cap = 3
PI = arb.pi()
WORDS = ["".join(w) for n in range(6) for w in itertools.product("+-", repeat=n)]
CASES = [(m, w) for m in range(-5, 6) for w in WORDS]
PACKETS = "blind-packets.json"
CALLS = "blind-calls.json"
REVEAL = "blind-reveal.json"
RESULTS = "blind-results.json"
PROTOCOL = Path(__file__).with_name("protocol.md")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(value):
    data = json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(data.encode()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path, data, rows_key=None):
    # For the two large tables one line per observation is easy to inspect and diff.
    if rows_key is None:
        text = json.dumps(data, indent=2)
    else:
        header = {key: value for key, value in data.items() if key != rows_key}
        rows = ",\n".join("    " + json.dumps(row, separators=(",", ":"))
                          for row in data[rows_key])
        text = json.dumps(header, indent=2)[:-2] + ',\n  "' + rows_key + '": [\n' + rows + "\n  ]\n}"
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text + "\n")


def encode(z):
    parts = [v.str(42) for v in (z.real, z.imag)]
    require(unpack(parts).contains(z), "Rounded text failed to enclose the original ball")
    return parts


def unpack(parts):
    return acb(arb(parts[0]), arb(parts[1]))


def direct(m, word):
    z = acb_series([1, 1], prec=3)
    for letter in word:
        factor = acb(0, (m if letter == "+" else -m) * PI)
        z = (z * factor).exp()
    return [encode(z[0]), encode(z[1]), encode(2 * z[2])]


def model(m, word):
    if not word:
        return (acb(1), acb(1), acb(0)), acb(0)
    if m == 0:
        return (acb(1), acb(0), acb(0)), None
    s = -1 if m % 2 else 1
    t = acb(0, s * m * PI)
    prefix, total = acb(1), acb(0)
    for letter in word:
        prefix *= t if letter == "+" else -t
        total += prefix
    ratio = s * total
    return (acb(s), prefix, prefix * ratio), ratio


def assignment(seed):
    return sorted(range(len(CASES)), key=lambda index: digest([seed, CASES[index]]))


def protocol_hash():
    # Normalize line endings so a Git checkout with CRLF also verifies.
    return hashlib.sha256(PROTOCOL.read_text(encoding="utf-8").encode()).hexdigest()


def prepare(folder, seed):
    folder.mkdir(parents=True, exist_ok=True)
    for name in (PACKETS, CALLS, REVEAL, RESULTS):
        require(not (folder / name).exists(), f"{name} already exists. Choose a fresh trial directory.")
    require(len(bytes.fromhex(seed)) == 32, "The seed must have 32 bytes")
    order = assignment(seed)
    key = {"seed": seed}
    packets = {"protocol_sha256": protocol_hash(), "commitment": digest([seed, order]),
               "schema": ["value", "first_derivative", "second_derivative"],
               "id": "zero-based row number", "precision_bits": ctx.prec,
               "flint_version": flint.__version__, "rows": [direct(*CASES[i]) for i in order]}
    write(folder / PACKETS, packets, "rows")
    write(folder / REVEAL, key)


def flip(word):
    return word.translate(str.maketrans("+-", "-+"))


def quotient(jet):
    _, slope, second = jet
    if slope.is_zero():
        return None
    require(not slope.contains(0), "Indeterminate denominator")
    return second / slope


def constructive(ratio):
    if ratio is None:
        return ["zero lift, nonempty"], None
    axes = sorted((abs(ratio.real), abs(ratio.imag)), key=lambda v: v.mid())
    small, large = axes
    if large < 1:
        require(small < 1, "Indeterminate empty word")
        return ["empty"], None
    require(large > 1, "Indeterminate axis")
    if small < 1:
        estimate = abs(ratio) / PI
    else:
        require(small > 1 and large > small, "Indeterminate axis ordering")
        estimate = large / (small * PI)
    half = arb(1) / 2
    nearest = (estimate + half).floor().unique_fmpz()
    require(nearest is not None, "Ambiguous nearest integer")
    q = int(nearest)
    error = abs(estimate - q)
    require(q > 0 and error < half, "Uncertified lift magnitude")
    r = q * PI
    n, power = 1, r
    while large > power * r / 2:
        n += 1
        power *= r
    require(power / 2 < large < power * r / 2, "Indeterminate length")
    s = -1 if q % 2 else 1
    t = acb(0, s * r)
    residual = s * ratio
    descending = []
    for j in range(n, 0, -1):
        term = t**j
        projection = (residual / term).real
        require(projection > 0 or projection < 0, "Indeterminate prefix sign")
        sign = 1 if projection > 0 else -1
        descending.append(sign)
        residual -= sign * term
    require(residual.contains(0), "Recovered coefficients fail the polynomial check")
    prefixes = [1, *reversed(descending)]
    word = "".join("+" if a == b else "-" for a, b in zip(prefixes, prefixes[1:]))
    return [q, word], error.upper()


def decode(packets):
    require(packets["protocol_sha256"] == protocol_hash(), "Protocol has changed")
    models = [model(m, w) for m, w in CASES]
    groups, group_ids, rows = [], {}, []
    counts = Counter()
    errors = {}
    minimum_gap = None

    def group_id(matches):
        signature = tuple(matches)
        if signature not in group_ids:
            group_ids[signature] = len(groups)
            groups.append(list(signature))
        return group_ids[signature]

    for row in packets["rows"]:
        jet = [unpack(v) for v in row]
        observed = quotient(jet)
        call, error = constructive(observed)
        if error is not None:
            q = call[0]
            errors[q] = max(errors.get(q, arb(0)), error)
        ratios, joints = [], []
        for i, (expected_jet, expected) in enumerate(models):
            if observed is None or expected is None:
                compatible = observed is expected
                counts["both_undefined" if compatible else "different_domains"] += 1
            else:
                compatible = observed.overlaps(expected)
                counts["finite_overlap" if compatible else "finite_disjoint"] += 1
                if not compatible:
                    gap = abs(observed - expected).lower()
                    require(gap > 0, "Uncertified finite rejection")
                    if minimum_gap is None or gap < minimum_gap:
                        minimum_gap = gap
            if compatible:
                ratios.append(i)
            joint = all(a.overlaps(b) for a, b in zip(jet, expected_jet))
            counts["raw_jet_overlap" if joint else "raw_jet_disjoint"] += 1
            if joint:
                joints.append(i)
        rows.append([group_id(ratios), group_id(joints), call])
    return {"packets_sha256": digest(packets), "schema": ["ratio_group", "raw_jet_group", "constructive"],
            "group_members": groups, "candidate_indices": "63*(m+5) + word index: lengths 0..5, + before -",
            "counts": dict(sorted(counts.items())),
            "wrong_finite_K_distance_lower_bound": minimum_gap.str(20),
            "maximum_rounding_error_upper_by_positive_lift": {str(q): v.str(18) for q, v in sorted(errors.items())},
            "rows": rows}


def score(folder):
    packets, calls, key = (read(folder / name) for name in (PACKETS, CALLS, REVEAL))
    order = assignment(key["seed"])
    require(digest([key["seed"], order]) == packets["commitment"], "Assignment commitment failed")
    require(decode(packets) == calls, "Archived calls do not replay")
    require(len(order) == len(packets["rows"]) == len(calls["rows"]), "Missing rows")
    groups = calls["group_members"]
    orbit_counts, examples = Counter(), []
    lookup = {case: i for i, case in enumerate(CASES)}
    for tag, index in enumerate(order):
        m, w = CASES[index]
        require(direct(m, w) == packets["rows"][tag], "Direct readings do not replay")
        if not w:
            orbit = {lookup[(a, "")] for a in range(-5, 6)}
            answer = ["empty"]
        elif m == 0:
            orbit = {lookup[(0, word)] for word in WORDS if word}
            answer = ["zero lift, nonempty"]
        else:
            orbit = {index, lookup[(-m, flip(w))]}
            answer = [abs(m), w if m > 0 else flip(w)]
        rg, jg, reconstructed = calls["rows"][tag]
        require(set(groups[rg]) == set(groups[jg]) == orbit, f"False or missing label at {tag}")
        require(reconstructed == answer, f"Constructive mismatch at {tag}")
        orbit_counts[len(orbit)] += 1
        if abs(m) == 4 and w in ("-----", "+++++"):
            examples.append({"id": tag, "m": m, "word": w, "positive_lift_reading": reconstructed,
                             "group": rg, "K": encode(quotient([unpack(v) for v in packets["rows"][tag]]))})
    return {"passed": True, "precision_bits": ctx.prec, "flint_version": flint.__version__,
            "observations": len(order), "candidate_checks_per_channel": len(order)**2,
            "nonempty_nonzero_cases": orbit_counts[2], "nonempty_nonzero_orbits": orbit_counts[2] // 2,
            "empty_observations": orbit_counts[11], "nonempty_zero_lift_observations": orbit_counts[62],
            "distinct_groups_including_controls": len(groups), "counts": calls["counts"],
            "wrong_finite_K_distance_lower_bound": calls["wrong_finite_K_distance_lower_bound"],
            "maximum_rounding_error_upper_by_positive_lift": calls["maximum_rounding_error_upper_by_positive_lift"],
            "correct_constructive_calls_including_controls": len(order),
            "all_minus_and_global_flip_examples": sorted(examples, key=lambda v: (v["m"], v["word"])),
            "protocol_sha256": packets["protocol_sha256"], "assignment_commitment": packets["commitment"],
            "packets_sha256": digest(packets), "calls_sha256": digest(calls)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "decode", "reveal", "verify"))
    parser.add_argument("--folder", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--seed", help="Optional 64 hexadecimal digits for a reproducible fresh assignment")
    args = parser.parse_args()
    require(flint.__version__ == "0.9.0", "Use python-flint 0.9.0 for exact transcript replay")
    if args.action == "prepare":
        prepare(args.folder, args.seed or secrets.token_hex(32))
    elif args.action == "decode":
        write(args.folder / CALLS, decode(read(args.folder / PACKETS)), "rows")
    else:
        results = score(args.folder)
        if args.action == "reveal":
            write(args.folder / RESULTS, results)
        else:
            require(results == read(args.folder / RESULTS), "Published summary differs from replay")
        print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
