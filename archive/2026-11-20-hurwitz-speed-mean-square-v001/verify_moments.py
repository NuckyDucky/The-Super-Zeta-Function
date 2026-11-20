"""Enclose the squared normalized Hurwitz speed in the three Dottie windows."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import platform

import flint
from flint import acb, acb_series, arb, ctx, dirichlet_char, fmpq


PREVIOUS = Path(__file__).resolve().parents[1] / "2026-11-20-liu-angular-velocity-v002"
BRACKETS_SHA256 = "13313056f1839349187a8bffe67268df160f8440dd48be4ca9ef729ad69d65a6"
PRECISION = 160
PRIME_CUTOFF = 1_000_000
COVER_CUTOFF = 2000
COVER_PIECES = 48
SERIES_CUTOFF = 65_536


def exact(value):
    rat = Fraction(value)
    return arb(fmpq(rat.numerator, rat.denominator))


def decimal_enclosure(value, digits=6):
    scale = 10**digits
    lo = int((value.lower() * scale).floor().unique_fmpz())
    hi = int((value.upper() * scale).ceil().unique_fmpz())

    def decimal(tick):
        sign = "-" if tick < 0 else ""
        whole, part = divmod(abs(tick), scale)
        return f"{sign}{whole}.{part:0{digits}d}"

    return [decimal(lo), decimal(hi)]


def primes_upto(cutoff):
    sieve = bytearray(b"\x01") * (cutoff + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(cutoff) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = bytes(1 + (cutoff - start) // p)
    return [n for n in range(2, cutoff + 1) if sieve[n]]


def local_factor(u, cosine):
    # |1-u*exp(i*theta)|^2 in a form positive even for a wide phase interval.
    return (1 - u)**2 + 2 * u * (1 - cosine)


def prime_enclosures(heights, cutoff):
    """Every t is a real Arb interval; here all zeros have real part 1/2."""
    products = [local_factor(1 / arb(3).sqrt(), (t * arb(3).log()).cos()) for t in heights]
    tail = (arb(3) / 2).zeta()
    for p in primes_upto(cutoff):
        prime = arb(p)
        u = 1 / (prime * prime.sqrt())
        tail *= 1 - u
        if p == 3:
            continue
        logp = prime.log()
        sign = 1 if p % 3 == 1 else -1
        for j, t in enumerate(heights):
            products[j] *= local_factor(u, sign * (t * logp).cos())

    tail_interval = (1 / tail**2).union(tail**2)
    scale = 9 / arb.pi()**2
    if not all(product > 0 for product in products):
        raise ArithmeticError("Subdivide the ordinate intervals to resolve the denominator.")
    return [scale / product * tail_interval for product in products], tail


def dottie_inputs():
    text = (PREVIOUS / "windows.json").read_bytes()
    if sha256(text).hexdigest() != BRACKETS_SHA256:
        raise ValueError("The input brackets differ from the reviewed archive.")
    eta = exact("4.749479070945369e-8")
    y = exact("0.509892982511772")
    td = arb.pi() / (80 * ((eta/y)**2).log1p())
    windows = []
    heights = []
    centers = []
    cover = []
    for window in json.loads(text)["windows"]:
        k = window["multiple_of_T_D"]
        center = k * td
        centers.append(center)
        width = Fraction(window["half_width"])
        pairs = window["hardy_brackets"]
        if window["N_upper"] - window["N_lower"] != len(pairs):
            raise ValueError("Incomplete list of zero brackets.")
        for pair in pairs:
            left, right = map(exact, pair["offsets"])
            if pair["signs"][0] * pair["signs"][1] != -1 or not left < right:
                raise ValueError("Invalid Hardy bracket.")
            heights.append(center + left.union(right))
        for j in range(COVER_PIECES):
            left = width * (2 * j - COVER_PIECES) / COVER_PIECES
            right = left + 2 * width / COVER_PIECES
            cover.append(center + exact(left).union(exact(right)))
        windows.append((k, width, window["N_lower"], len(pairs)))
    return windows, heights, centers, cover


def independent_series(heights):
    """Use the defining Dirichlet sum and its absolute tail on the critical line."""
    sums = [acb(0) for _ in heights]
    for n in range(1, SERIES_CUTOFF + 1):
        if n % 3 == 0:
            continue
        base = arb(n)
        factor = (1 if n % 3 == 1 else -1) / (base * base.sqrt())
        logn = base.log()
        for j, t in enumerate(heights):
            sums[j] += factor * acb(0, -t * logn).exp()
    error = arb(0, 2 / arb(SERIES_CUTOFF).sqrt())
    result = []
    for value, t in zip(sums, heights, strict=True):
        magnitude = abs(value) + error
        if not magnitude > 0:
            raise ArithmeticError("The independent sum needs a larger cutoff.")
        divisor = abs(1 - acb(3)**(-acb(arb(1)/2, t)))
        result.append((3 * magnitude / (arb.pi() * divisor))**2)
    return result


def prime_bias(chi, diagonal):
    series = acb_series([2, 1], prec=2).dirichlet_l(chi)
    ld = series[1] / series[0]
    if not ld.imag.contains(0):
        raise ArithmeticError("The logarithmic derivative must be real at two.")
    bias = diagonal * (arb(3).log() - 2 * ld.real)
    partial = arb(3).log() / 2
    for p in primes_upto(SERIES_CUTOFF):
        if p != 3:
            sign = 1 if p % 3 == 1 else -1
            partial += sign * arb(p).log() / (p*p - sign)
    x = arb(SERIES_CUTOFF)
    tail = (x.log() + 1) / (x * (1 - x**-2))
    independent = 2 * diagonal * (partial + arb(0, tail))
    if not independent.contains(bias) or not independent > 0:
        raise ArithmeticError("The absolutely bounded prime sum did not verify the bias.")
    return bias, independent


def low_means(chi, sixth_product, diagonal, bias):
    report = {}
    total = arb(0)
    sixth = None
    for i, rho in enumerate(acb.zeta_zeros(1, 1024), start=1):
        if rho.real != arb(1) / 2:
            raise ArithmeticError(f"Critical-line check failed at zero {i}.")
        taylor = acb_series([rho, 1], prec=2).zeta()
        if not taylor[0].contains(0) or taylor[1].contains(0):
            raise ArithmeticError(f"Simple-zero check failed at zero {i}.")
        q = (1 + rho).dirichlet_l(chi) / (1 - acb(3)**(-rho))
        sample = abs(3 * q / arb.pi())**2
        total += sample
        if i == 6:
            sixth = (rho.imag, sample)
        if i in (64, 256, 1024):
            report[str(i)] = {
                "observed": decimal_enclosure(total / i, 10),
                "two_term_formula": decimal_enclosure(diagonal - bias*rho.imag/(2*arb.pi()*i), 10),
            }
    if sixth is None or not sixth[1].overlaps(sixth_product):
        raise ArithmeticError("Prime-product check disagrees with the direct L-value at zero 6.")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.prec = PRECISION
    windows, heights, centers, cover = dottie_inputs()
    high, tail = prime_enclosures(heights + centers + [acb.zeta_zero(6).imag], PRIME_CUTOFF)
    covers, cover_tail = prime_enclosures(cover, COVER_CUTOFF)
    chi = dirichlet_char(3, 2)
    samples = high[:len(heights)]
    center_values = high[len(heights):-1]
    series_check = independent_series(heights)
    if not all(a.overlaps(b) for a, b in zip(samples, series_check, strict=True)):
        raise ArithmeticError("An Euler-product enclosure disagrees with its Dirichlet-series check.")
    z3 = arb(3).zeta()
    q_second = 13 * z3 / 9
    speed_second = 13 * z3 / arb.pi()**2
    inverse_second = arb.pi()**2 * z3 / (7 * arb(6).zeta())
    bias, bias_check = prime_bias(chi, speed_second)
    low = low_means(chi, high[-1], speed_second, bias)
    out = []
    first = 0
    for j, (k, half_width, count_lower, count) in enumerate(windows):
        block = samples[first:first + count]
        pieces = covers[j * COVER_PIECES:(j + 1) * COVER_PIECES]
        all_t = pieces[0]
        for piece in pieces[1:]:
            all_t = all_t.union(piece)
        mean = sum(block, arb(0)) / count
        if not all(all_t.contains(x) for x in [*block, center_values[j], mean]):
            raise ArithmeticError("The window cover and the individual evaluations disagree.")
        out.append({"k": k, "half_width": str(half_width), "zero_count": count,
                    "mean_S_squared": decimal_enclosure(mean),
                    "center_S_squared": decimal_enclosure(center_values[j]),
                    "mean_minus_center_S_squared": decimal_enclosure(mean - center_values[j]),
                    "mean_quotient_squared": decimal_enclosure(mean * (arb.pi()/3)**2),
                    "bound_on_S_squared_over_the_whole_vertical_segment": decimal_enclosure(all_t),
                    "individual_S_squared": {str(count_lower+i): decimal_enclosure(value)
                                             for i, value in enumerate(block, 1)},
                    "independent_Dirichlet_series_S_squared": [
                        decimal_enclosure(value) for value in series_check[first:first + count]]})
        first += count
    report = {"python": platform.python_version(), "python_flint": flint.__version__,
              "flint": flint.__FLINT_VERSION__, "precision_bits": PRECISION,
              "brackets_sha256": BRACKETS_SHA256, "prime_cutoff": PRIME_CUTOFF,
              "independent_series_cutoff": SERIES_CUTOFF,
              "upper_tail_product": decimal_enclosure(tail, 12), "cover_cutoff": COVER_CUTOFF,
              "cover_pieces": COVER_PIECES, "cover_upper_tail_product": decimal_enclosure(cover_tail, 12),
              "diagonal_quotient_squared": decimal_enclosure(q_second, 13),
              "diagonal_S_squared": decimal_enclosure(speed_second, 13),
              "diagonal_inverse_S_squared": decimal_enclosure(inverse_second, 13),
              "prime_power_bias_K": decimal_enclosure(bias, 13),
              "independent_partial_prime_sum_for_K": decimal_enclosure(bias_check, 8),
              "simple_bounds_kappa_two_thirds": {
                  "lower": decimal_enclosure(exact("2/3") / inverse_second, 12),
                  "upper": decimal_enclosure(speed_second / exact("2/3"), 12)},
              "windows": out, "all_11_mean_S_squared": decimal_enclosure(sum(samples, arb(0)) / len(samples)),
              "first_n_simple_zeros_mean_S_squared": low}
    value = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(value, encoding="utf-8", newline="\n")
    else:
        print(value, end="")


if __name__ == "__main__":
    main()

