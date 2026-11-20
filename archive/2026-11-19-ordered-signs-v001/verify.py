"""Directed disk and derivative tests for two cap-selected period-640 minima.

Run with Python 3.12 and python-flint 0.9.0. Only the final JSON is printed.
All tabulated input decimals, including interval endpoints, are rational.
"""
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction

from flint import acb, arb, ctx, fmpq

PERIOD = 640
TRAP_RADIUS = Fraction(1, 10**6)
FIRST = Fraction("0.5098929835386691077069064221391756841")
SECOND = Fraction("0.5098930237333223092469862115108741354")
BAND = (Fraction("0.5098930229215867"), Fraction("0.50989302375"))


def real(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


@dataclass(frozen=True)
class Disk:
    center: acb
    radius: arb

    @classmethod
    def enclose(cls, box, error=0):
        """Enclose the rounding of the center and add the specified disk error."""
        box = acb(box)
        c = box.mid()
        return cls(c, (abs(box - c) + error).upper())

    def __add__(self, other):
        return Disk.enclose(self.center + other.center, self.radius + other.radius)

    def __neg__(self):
        return Disk(-self.center, self.radius)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        error = (abs(self.center) * other.radius + abs(other.center) * self.radius
                 + self.radius * other.radius)
        return Disk.enclose(self.center * other.center, error)

    def inv(self):
        m = abs(self.center)
        check(m > self.radius, "disk inversion touches zero")
        return Disk.enclose(1 / self.center, self.radius / (m * (m - self.radius)))

    def exp(self):
        value = self.center.exp()
        return Disk.enclose(value, abs(value) * self.radius.expm1())

    def upper(self):
        return (abs(self.center) + self.radius).upper()

    def lower(self):
        return (abs(self.center) - self.radius).lower()

    def re(self):
        return self.center.real + arb(0, self.radius)


def parameter(lo, hi):
    check(lo <= hi, "reversed parameter interval")
    return Disk.enclose(real((lo + hi) / 2), real((hi - lo) / 2))


def stages(y):
    unit = Disk.enclose(acb(0, 1))
    return ((-unit, (-unit) * y), (unit, unit * y))


def lap(z, y):
    signs = stages(y)
    states = [z]
    for j in range(PERIOD):
        states.append((signs[j % 2][1] * states[-1]).exp())
    return states, signs


def trap():
    return Disk.enclose(1, real(TRAP_RADIUS))


def fold_gauge():
    """The frozen gate used for the scalar itinerary in the Dottie supplement."""
    middle = Fraction("0.739085133215160641655312087673873404")
    radius = Fraction(1, 10**35)
    lo, hi = real(middle-radius), real(middle+radius)
    check(lo < lo.cos() and hi > hi.cos(), "Dottie root bracket undecided")
    d = parameter(middle-radius, middle+radius).re()
    alpha = acb(d.sin(), d)
    z_star = Disk.enclose(alpha.exp())
    beta = Disk.enclose((1+alpha) * acb(0, -(-d.sin()).exp()) / 2)
    return beta, z_star


def gate_word(states, gauge):
    """One gate decision per scalar update, using the marked phase in the cap disk."""
    beta, z_star = gauge
    outside, margins = [], []
    threshold = real(Fraction(8, 100))
    for j, z in enumerate(states[:-1:2]):
        distance = beta * (z - z_star)
        if distance.lower() > threshold:
            outside.append(j)
            margins.append(distance.lower() - threshold)
        else:
            check(distance.upper() < threshold, f"gate unresolved at scalar index {j}")
            margins.append(threshold - distance.upper())
    return outside, min(m.lower() for m in margins)


def manuscript_disk():
    # REAL_POINT_UPPER of supplement P3K-640, certify_directed_continuation.py.
    cr = real("0.9999996034350764449934984731487192190650492742771112156224878231833240620969743881749190567758854070263828923298486599100034104044")
    ci = real("-0.0000001191519344021400351588601191161565614732733443814413725778806332475534499140895987336122841516489922291358046225827550586563764468")
    slack = real("0.0007") - abs(acb(cr, ci)-1) - real(TRAP_RADIUS)
    check(slack > 0, "cap disk must lie inside the manuscript continuation disk")
    return slack.lower().str(12)


def detuning(y, center_y):
    """Certify the nonreal inverse with positive imaginary part near the Dottie fold."""
    def value(u):
        return u / u.cos() * (-u * u.tan()).exp()

    def derivative(u):
        return value(u) * (1/u - u/u.cos()**2)

    c = acb(real("0.73909"), real("0.00434"))
    for _ in range(8):
        c = (c - (value(c)-real(center_y))/derivative(c)).mid()
    radius = real("1e-21")
    box = c + acb(arb(0, radius), arb(0, radius))
    A = (1 / derivative(c)).mid()
    lip = abs(1 - A * derivative(box))
    residual = abs(A * (value(c)-y.re()))
    check(lip < 1 and residual + radius * lip < radius and box.imag > 0,
          "could not enclose the upper local inverse")
    epsilon = box / box.cos()
    check(epsilon.real > 0, "principal logarithm meets the cut")
    lam = 2 * epsilon.log()
    delta = PERIOD - 4 * arb.pi() * abs((1 / lam).imag)
    return {"upper_u": [box.real.str(18), box.imag.str(18)],
            "delta": delta.str(16)}


def adjacent_readings(y):
    states, signs = fixed_orbit(y)
    # The last stage and one extra stage give a reading for the first sign
    # on the next lap. The marked phase is a fixed point of the full lap.
    states.append((signs[0][1] * states[-1]).exp())
    prefix = [Disk.enclose(1)]
    for j, dest in enumerate(states[1:]):
        prefix.append(prefix[-1] * (signs[j % 2][1] * dest))
    worst_rate = arb(0)
    worst_state = arb(0)
    for j in range(1, PERIOD+1):
        d1 = prefix[j] * prefix[j-1].inv()
        d2 = prefix[j+1] * prefix[j].inv()
        # Rates alternate, so the next actual exponent is -d1.
        state = (-d1).exp()
        rate = d2 * d1.exp()
        expected = signs[j % 2][1]
        worst_rate = max(worst_rate, (rate - expected).upper())
        worst_state = max(worst_state, (state - states[j+1]).upper())
        check((rate-expected).upper() < y.re() and (rate+expected).lower() > y.re(),
              f"stage sign unresolved at stage {j+1}")
    check(worst_state < real("1e-6"), "stage recovery lost precision")
    return {"stages_read": PERIOD, "first_recovered_stage": 2,
            "last_recovered_stage": PERIOD+1,
            "max_rate_error_upper": worst_rate.str(12),
            "max_state_error_upper": worst_state.str(12)}


def sliding_readings(y):
    """Read the 160/161 derivative windows from consecutive starting phases."""
    states, signs = fixed_orbit(y)
    width = 160
    rates = [signs[j % 2][1] for j in range(PERIOD)]
    factors = [a * z for a, z in zip(rates, states[1:])]
    exponents = [a * z for a, z in zip(rates, states[:-1])]
    # Any 160 stages contain 80 rates of each sign.
    rate_product = Disk.enclose(1)
    for _ in range(width // 2):
        rate_product = rate_product * (rates[0] * rates[1])

    ratios = []
    for j in range(PERIOD):
        short = Disk.enclose(1)
        total = Disk.enclose(0)
        for k in range(j, j+width):
            short = short * factors[k % PERIOD]
            total = total + exponents[k % PERIOD]
        end = (j+width) % PERIOD
        # Independent formulas compute the two window derivatives. The longer
        # one uses the sum of the actual exponents, the shorter the chain rule.
        long = (rate_product * rates[end]) * (total + exponents[end]).exp()
        ratios.append(long * short.inv())

    readings = [(ratios[(j+1) % PERIOD] * ratios[j].exp(), (-ratios[j]).exp())
                for j in range(PERIOD)]
    worst_rate, worst_state = arb(0), arb(0)
    for j, (rate, state) in enumerate(readings):
        end = (j+width+1) % PERIOD
        error = (rate-rates[end]).upper()
        check(error < y.re() and (rate+rates[end]).lower() > y.re(),
              f"sliding windows failed to distinguish stage {end+1}")
        worst_rate = max(worst_rate, error)
        worst_state = max(worst_state, (state-states[end+1]).upper())
    check(worst_state < real("1e-6"), "sliding windows lost output precision")
    return {"lengths": [width, width+1], "starting_phases": PERIOD,
            "max_rate_error_upper": worst_rate.str(12),
            "max_state_error_upper": worst_state.str(12)}


def verify_trap(y, gauge=None):
    D = trap()
    states, signs = lap(D, y)
    image_radius = (abs(states[-1].center - D.center) + states[-1].radius).upper()
    lip = arb(1)
    for j, dest in enumerate(states[1:]):
        lip = (lip * signs[j % 2][1].upper() * dest.upper()).upper()
    # 640 = 2^7 * 5. Both exclusion indices are even, where the signed
    # scalar prefixes agree with the physical centerline half-step iterates.
    gap = min((states[k] - D).lower() for k in (320, 128))
    check(image_radius < real(TRAP_RADIUS) and lip < 1 and gap > 0,
          "failed cap trap, contraction, or primitive-period exclusion")
    if gauge is None:
        return image_radius, lip, gap
    outside, margin = gate_word(states, gauge)
    expected = list(range(11)) + list(range(306, 320))
    check(outside == expected, f"different gate word: {outside}")
    return image_radius, lip, gap, margin


def band_proof(lo, hi, pieces):
    bounds = []
    gauge = fold_gauge()
    for i in range(pieces):
        l = lo + (hi - lo) * i / pieces
        r = lo + (hi - lo) * (i+1) / pieces
        bounds.append(verify_trap(parameter(l, r), gauge))
    return {"tiles": pieces, "lower_y": str(lo), "upper_y": str(hi),
            "image_radius_upper": max(b[0] for b in bounds).str(12),
            "lipschitz_upper": max(b[1] for b in bounds).str(12),
            "proper_divisor_gap_lower": min(b[2] for b in bounds).str(12),
            "manuscript_disk_inclusion_slack": manuscript_disk(),
            "outside_scalar_indices": [[0, 10], [306, 319]],
            "gate_distance_margin_lower": min(b[3] for b in bounds).str(12)}


def fixed_orbit(y):
    # Each image of the common trapping disk still contains its fixed point.
    phase = trap()
    for _ in range(14):
        phase = lap(phase, y)[0][-1]
    return lap(phase, y)


def modulus_jets(y):
    """Derivatives along the closed branch, including the motion of its phase."""
    states, rates = fixed_orbit(y)
    zero, one, two = map(Disk.enclose, (0, 1, 2))
    mu, partial_y = one, zero
    for j, (z, dest) in enumerate(zip(states, states[1:])):
        sign_i, a = rates[j % 2]
        mu = (a * dest) * mu
        partial_y = dest * (sign_i * z + a * partial_y)
    inverse = (one - mu).inv()
    v0 = inverse * partial_y

    # First solve for z'_0, then differentiate the closure a second time.
    # With initial acceleration zero, the terminal acceleration is the
    # inhomogeneous part of that second closure equation.
    def propagate(acceleration):
        v, w, sum1, sum2 = v0, acceleration, zero, zero
        for j, (z, dest) in enumerate(zip(states, states[1:])):
            sign_i, a = rates[j % 2]
            du = sign_i * z + a * v
            ddu = two * sign_i * v + a * w
            sum1, sum2 = sum1 + du, sum2 + ddu
            v, w = dest * du, dest * (du * du + ddu)
        return w, sum1.re(), sum2.re()

    forcing, _, _ = propagate(zero)
    _, first, second = propagate(inverse * forcing)
    yr = y.re()
    return (PERIOD / yr + first, second - PERIOD / (yr * yr),
            abs(mu.center) + arb(0, mu.radius), states[0])


def certify_minimum(center, halfwidth):
    left, right = center - halfwidth, center + halfwidth
    verify_trap(parameter(left, right))
    left_slope = modulus_jets(parameter(left, left))[0]
    right_slope = modulus_jets(parameter(right, right))[0]
    _, curvature, modulus, phase = modulus_jets(parameter(left, right))
    check(left_slope < 0 and right_slope > 0 and curvature > 0,
          f"stationarity undecided: {left_slope}, {right_slope}, {curvature}")
    check(modulus > 0 and modulus < 1, "multiplier modulus must lie in (0,1)")
    return {"center_y": str(center), "y_halfwidth": str(halfwidth),
            "left_log_modulus_slope": left_slope.str(14),
            "right_log_modulus_slope": right_slope.str(14),
            "log_modulus_curvature": curvature.str(15), "modulus": modulus.str(15),
            "cap_phase_real": phase.re().str(20),
            "unfolding": detuning(parameter(left, right), center),
            "cap_phase_imag": (phase.center.imag + arb(0, phase.radius)).str(20)}


def example_words(y):
    from itertools import combinations
    words = {}
    for pos in combinations(range(4), 2):
        word = ''.join('+' if k in pos else '-' for k in range(4))
        z = Disk.enclose(1)
        rates = stages(y)
        for ch in word:
            z = (rates[ch == '+'][1] * z).exp()
        for other in words.values():
            check((z - other).lower() > 0, "two four-stage disk enclosures overlap")
        words[word] = z
    return {w: [z.re().str(12), (z.center.imag + arb(0, z.radius)).str(12)]
            for w,z in words.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=384)
    args = parser.parse_args()
    ctx.prec = args.bits
    halfwidth = Fraction(1, 10**24)
    records = {"precision_bits": ctx.prec, "paired_period": PERIOD,
               "scalar_period": PERIOD // 2, "trap_center": 1,
               "trap_radius": str(TRAP_RADIUS), "continuation": band_proof(*BAND, 32),
               "first_minimum": certify_minimum(FIRST, halfwidth),
               "second_minimum": certify_minimum(SECOND, halfwidth),
               "adjacent_derivative_recovery": adjacent_readings(parameter(SECOND-halfwidth, SECOND+halfwidth)),
               "sliding_derivative_recovery": sliding_readings(parameter(SECOND-halfwidth, SECOND+halfwidth)),
               "balanced_words_at_second_minimum": example_words(
                   parameter(SECOND-halfwidth, SECOND+halfwidth))}
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
