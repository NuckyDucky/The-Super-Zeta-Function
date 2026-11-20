"""Branch-blind reconstruction. Python 3.10+; standard library only."""
import argparse
import hashlib
import json
import secrets
from fractions import Fraction as Q
from math import isqrt, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
CUT = 33
CONDUCTOR = ((41, 32), (457, 109), (1414835497, 516876951))
N = (-659, -183, 465)
D = (-936, 396, 155)
NAMES = {1: "A+2iN", -1: "A-2iN"}


def mark(a, b, side):
    """The conductor formula with the hidden branch, on the ideal (a+bi)."""
    def symbol(v, p):
        t = pow(v % p, (p - 1) // 2, p)
        return -1 if t == p - 1 else t
    return prod(symbol(a + side*b*t, p) for p, t in CONDUCTOR)


def times(z, w):
    return z[0]*w[0] - z[1]*w[1], z[0]*w[1] + z[1]*w[0]


def power(z, k):
    result = (1, 0)
    for _ in range(k):
        result = times(result, z)
    return result


def shell(n, side):
    scalar, angular = 0, Q(0)
    for a in range(1, isqrt(n) + 1):
        b = isqrt(n-a*a)
        if b*b + a*a == n:
            sign = mark(a, b, side)
            scalar += sign
            angular += Q(sign * power((a, b), 4)[1], n*n)
    return scalar, angular


def root_sign(p, a, b, side):
    """Independent reading from the original quadratic, including the root at infinity."""
    i_mod_p = -a * pow(b, -1, p) % p
    assert (i_mod_p*i_mod_p + 1) % p == 0
    c, h, k = [(x-y+side*2*i_mod_p*x) % p for x, y in zip(N, D)]
    assert any((c, h, k))
    roots = sum((c+h*t+k*t*t) % p == 0 for t in range(p)) + int(k == 0)
    return roots - 1


def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def log_second_shells(side):
    # Above 2 and inert rational primes the angular character is real.
    nonreal = {}
    for p in range(5, CUT+1, 4):
        if not prime(p):
            continue
        a, b = next((a, isqrt(p-a*a)) for a in range(1, isqrt(p)+1)
                    if isqrt(p-a*a)**2 == p-a*a)
        k, n = 1, p
        while n <= CUT:
            coefficient = Q(0)
            for j in (b, -b):
                sign = root_sign(p, a, j, side)
                coefficient += Q(k * sign**k * power((a, j), 4*k)[1], n*n)
            if coefficient:
                nonreal[n] = coefficient  # multiply by log(p)^2
            n *= p
            k += 1
    return nonreal


def log_from_ratio(x, terms=14):
    # log((1+x)/(1-x)) with a rational geometric bound for the tail.
    lower = 2*sum((x**(2*j+1)/(2*j+1) for j in range(terms)), Q(0))
    return lower, lower + 2*x**(2*terms+1)/((2*terms+1)*(1-x*x))


def log17_interval():
    a, b = log_from_ratio(Q(1, 3))
    c, d = log_from_ratio(Q(1, 33))
    return 4*a+c, 4*b+d


def enclose(lo, hi):
    # Outward-rounded endpoints, with six exact decimal places.
    def show(scaled):
        return f"{'-' if scaled < 0 else ''}{abs(scaled)//10**6}.{abs(scaled)%10**6:06d}"
    return [show((lo*10**6).__floor__()), show((hi*10**6).__ceil__())]


def measurements(side):
    rows = [shell(n, side) for n in range(1, CUT+1)]
    scalar = [re for re, _ in rows]
    partial = sum((im * Q(17, n)**8 for n, (_, im) in enumerate(rows, 1)), Q(0))
    tail = Q(17**8, 6*CUT**6)
    log_terms = log_second_shells(side)
    if set(log_terms) != {17}:
        raise ArithmeticError("Unexpected support in the Euler moment through norm 33")
    a, b = log17_interval()
    lo, hi = sorted((log_terms[17]*a*a, log_terms[17]*b*b))
    moment_tail = Q(17**16, 13*CUT**13)
    return {"unmarked_coefficients_through_33": scalar,
            "imag_angular_value_times_17pow8": enclose(partial-tail, partial+tail),
            "zero_moment_times_17pow16_from_euler_side": enclose(lo-moment_tail, hi+moment_tail)}


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def reveal_hash(reveal):
    return hashlib.sha256(json.dumps(reveal, sort_keys=True).encode()).hexdigest()


def prepare(folder):
    slots = [1, -1]
    secrets.SystemRandom().shuffle(slots)
    truth = {tag: NAMES[side] for tag, side in zip(("A", "B"), slots)}
    reveal = {"nonce": secrets.token_hex(16), "labels": truth}
    cases = {tag: measurements(side) for tag, side in zip(("A", "B"), slots)}
    write(folder / "sealed-input.json", {"commitment": reveal_hash(reveal), "cases": cases})
    write(folder / "reveal.json", reveal)


def decode(blind):
    # Input consists solely of the anonymized interval readings and equal scalar data.
    def classify(pair):
        lo, hi = map(Q, pair)
        if lo > 0:
            return NAMES[1]
        if hi < 0:
            return NAMES[-1]
        return "unresolved"
    cases = blind["cases"]
    assert cases["A"]["unmarked_coefficients_through_33"] == cases["B"]["unmarked_coefficients_through_33"]
    return {tag: {"scalar": "both branches compatible",
                  "angular_series": classify(data["imag_angular_value_times_17pow8"]),
                  "completed_zero_moment": classify(data["zero_moment_times_17pow16_from_euler_side"])}
            for tag, data in cases.items()}


def verify(folder):
    blind, reveal = read(folder / "sealed-input.json"), read(folder / "reveal.json")
    assert blind["commitment"] == reveal_hash(reveal)
    assert set(reveal["labels"]) == set(blind["cases"]) == {"A", "B"}
    assert set(reveal["labels"].values()) == set(NAMES.values())
    calls = read(folder / "calls.json")
    assert calls == decode(blind)
    # Drop the '+' / '-' probe labels. At real w the two samples are conjugates.
    for key in ("imag_angular_value_times_17pow8", "zero_moment_times_17pow16_from_euler_side"):
        def unlabelled(case):
            lo, hi = map(Q, case[key])
            return sorted([(lo, hi), (-hi, -lo)])
        assert unlabelled(blind["cases"]["A"]) == unlabelled(blind["cases"]["B"])
    records = {}
    for tag, actual in reveal["labels"].items():
        side = 1 if actual == NAMES[1] else -1
        assert blind["cases"][tag] == measurements(side)
        assert calls[tag]["angular_series"] == calls[tag]["completed_zero_moment"] == actual
        controls = {}
        for p, (a, b) in [(13,(2,3)), (37,(1,6)), (73,(3,8))]:
            signs = [root_sign(p, a, j, side) for j in (b,-b)]
            assert signs == [mark(a, j, side) for j in (b,-b)]
            controls[str(p)] = signs
        assert shell(73, side) == (0, side*Q(10560,5329))
        records[tag] = {"revealed": actual, "direct_sign_pairs": controls,
                        "imaginary_coefficient_at_73": str(shell(73, side)[1])}
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "decode", "verify"])
    parser.add_argument("--folder", type=Path, default=HERE)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Enable Python assertions to run this verification.")
    if args.action == "prepare":
        args.folder.mkdir(parents=True, exist_ok=True)
        if any((args.folder / name).exists() for name in ("sealed-input.json", "reveal.json", "calls.json")):
            parser.error("Use a fresh folder to start a new sealed trial.")
        prepare(args.folder)
    elif args.action == "decode":
        calls = decode(read(args.folder / "sealed-input.json"))
        write(args.folder / "calls.json", calls)
        print(json.dumps(calls, indent=2))
    else:
        print(json.dumps(verify(args.folder), indent=2))


if __name__ == "__main__":
    main()
