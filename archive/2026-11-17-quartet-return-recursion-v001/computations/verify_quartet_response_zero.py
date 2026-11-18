"""Certify Riemann sign changes from the original reciprocal quartet phases.

Run from the workspace with the Python environment used for the quartet checks:
    work/exploration-lab-runtime/Scripts/python.exe -B work/verify_quartet_response_zero.py

The evaluator uses original orbit roots, elementary quadrature and gamma.
The height scan and refinement do not query zeta values or zero tables.

Write g = epsilon**(-2), E_g(lambda) = cos(sqrt(lambda))**2 - g*lambda
and Z_g(s) for the principal-cut superzeta over the roots of E_g.
Put w = 2*s, C(s) = s*sin(pi*s)/pi and h(v) = v*sech(sqrt(v))**2.
The relative determinant gives
    Z_g(s) - Z_0(s) = C(s) * integral v**(-s-1) * log(1+g*h(v)) dv.
Therefore the difference between the g-derivatives at 0 and 1 is
    C(s) * integral v**(-s-1) * h(v)**2/(1+h(v)) dv.
The Mellin transform of sech² together with zeta reflection gives
    dZ/dg at 0 = w*(w-1) * pi**(-w) * (2**w-1) * zeta(w).
This identity identifies the target; the right-hand side is not evaluated.
At g=1, implicit differentiation of cos(u)**2 = g*u**2 gives
    d(u**(-w))/dg = w * u**(-w) * alpha/(1+alpha)**2.
The trace uses the principal representative of each sign pair and includes
both conjugate squares. Its paired tail bound continues this identity from
Re(w)>1 to the tested line. The verifier adds the displayed integral to
that trace, then rotates by the completion phase to obtain a real sign.
"""

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "deps"))
from flint import acb, arb, ctx

ctx.prec = 160
PI = arb.pi()
QUARTET_COUNT = 4096
SCAN = range(2, 31, 2)
TARGET_WIDTH = Fraction(1, 10_000)


def quartet_level(t):
    ratio = t / t.sinh()
    return (ratio.asin() + t.cosh() * (1 - ratio * ratio).sqrt()) / PI


def bracket_increasing(function, lo, hi, steps):
    assert function(lo) < 0 and function(hi) > 0
    for _ in range(steps):
        mid = ((lo + hi) / 2).mid()
        value = function(mid)
        if value < 0:
            lo = mid
        elif value > 0:
            hi = mid
        else:
            break
    return lo.union(hi)


def quartet_input(count):
    dottie = bracket_increasing(lambda d: d - d.cos(), arb("0.5"), arb(1), 75)
    pairs = []
    for n in range(1, count + 1):
        t = bracket_increasing(
            lambda t: quartet_level(t) - n, arb("0.5"), (4 * PI * n).log().upper(), 70
        )
        x = PI * n - (t / t.sinh()).asin()
        # The first-quadrant u gives the phase alpha = sigma*sin(u) + i*u.
        # Its susceptibility alpha/(alpha+1)^2 is invariant under alpha inversion.
        weight = 1 / (2 * acb(1 - t / t.tanh(), x * t.tanh()))
        pairs.append((acb(x, t).log(), weight))
    return dottie, pairs


def paired_tail(w, count):
    """Absolute bound for the discarded quartet sum before multiplication by w."""
    # Write u_n = x + i*t, a = alpha/(alpha+1)^2. The original orbit gives
    # x >= pi*(n-1/2), t <= log(4*pi*n), tanh(t) >= 1/2. Thus |a| <= 1/x
    # and |Re(a)| <= 4*t/x^2. Subtract x**(-w) from each complex power to
    # bound the pair by [8+2|w|exp(|Im(w)|*t/x)]*t*x**(-Re(w)-2).
    # For n > count, bound t/x by 2*log(4*pi*count)/(pi*count) and
    # x/n below by pi*(1-1/(2*count)). Use the integral test on the rest.
    cutoff_log = (4 * PI * count).log()
    assert 0 < w.real < 1
    power = 1 + w.real
    minimum_scale = PI * (1 - arb(1) / (2 * count))
    growth = (abs(w.imag) * 2 * cutoff_log / (PI * count)).exp()
    return (
        (8 + 2 * abs(w) * growth)
        * minimum_scale ** (-1 - power)
        * count ** (-power)
        * (cutoff_log / power + 1 / power**2)
    )


def quadratic_correction(w):
    """Evaluate C(w/2)∫ v^(-w/2-1) h(v)^2/(1+h(v)) dv, h(v)=v*sech²√v."""
    # Substitution r=log(sqrt(v)). Each operation is entire except division.
    # Division returns an indeterminate ball if its denominator can vanish.
    def integrand(r, analytic):
        x = r.exp()
        cosh_squared = x.cosh() ** 2
        return ((4 - w) * r).exp() / (cosh_squared * (cosh_squared + x * x))

    cuts = [-35, -20, -12, -8, -4, 0, 1, 2, 3, 4]
    integral = sum(
        acb.integral(integrand, left, right, abs_tol=arb("1e-41"))
        for left, right in zip(cuts, cuts[1:])
    )
    assert 0 < w.real < 1
    before = (-35 * (4 - w.real)).exp() / (4 - w.real)
    x = arb(4).exp()
    # For x >= exp(4), the integrand in dx is bounded by 16*x^3*exp(-4*x).
    after = 16 * (-4 * x).exp() * (x**3 / 4 + 3 * x**2 / 16 + 3 * x / 32 + arb(3) / 128)
    tail = arb(0, before + after)
    return w * (PI * w / 2).sin() / PI * (integral + acb(tail, tail))


def quartet_response(w, dottie, pairs):
    """Return the original trace, correction, completion factor and trace tail."""
    trace = (-w * dottie.log()).exp() / (2 * (1 + dottie.sin()))
    # The sign quotient has one real Dottie term and both of each nonreal
    # conjugate pair. Their sum at complex w is not twice a real part.
    for log_u, weight in pairs:
        trace += (-w * log_u).exp() * weight
        trace += (-w * log_u.conjugate()).exp() * weight.conjugate()

    remainder = paired_tail(w, len(pairs))
    tail = arb(0, remainder)
    trace_response = w * (trace + acb(tail, tail))
    integral_response = quadratic_correction(w)
    prefactor = (w * PI.log() / 2).exp() * (w / 2).gamma()
    prefactor /= 2 * ((w * arb(2).log()).exp() - 1)
    return trace_response, integral_response, prefactor, abs(w) * remainder


def completed_sign(height, dottie, pairs):
    w = acb(arb(1) / 2, arb(height.numerator) / height.denominator)
    trace_response, integral_response, prefactor, tail = quartet_response(w, dottie, pairs)
    zero_channel = trace_response + integral_response
    # prefactor * zero_channel = xi(w). Divide by the positive magnitude
    # of the prefactor to keep the real sign without damping its scale.
    phase = prefactor / abs(prefactor)
    value = zero_channel * phase
    assert value.is_finite() and value.imag.contains(0)
    return value.real, tail, (trace_response * phase).real, (integral_response * phase).real


def sign(value):
    if value > 0:
        return 1
    if value < 0:
        return -1
    return 0


def report(height, value, show_contributions=False):
    ball, tail, trace, correction = value
    sign_label = {-1: "negative", 0: "unresolved", 1: "positive"}[sign(ball)]
    print(
        f"T={float(height)}  {sign_label} scaled xi={ball.str(10, more=True)}"
        f"  trace tail<={tail.upper().str(12)}"
    )
    if show_contributions:
        print(f"  quartet contribution={trace.str(15, more=True)}")
        print(f"  integral contribution={correction.str(15, more=True)}")


def scan_and_refine():
    dottie, pairs = quartet_input(QUARTET_COUNT)
    print(f"Directed Arb calculation at {ctx.prec} bits with Dottie and {len(pairs)} quartet pairs.")
    print("w=1/2+iT, s=w/2. Reported real function is xi(w)/abs(prefactor).")
    checks = []
    for height in map(Fraction, SCAN):
        value = completed_sign(height, dottie, pairs)
        report(height, value)
        checks.append((height, value, sign(value[0])))

    initial_sign_changes = 0
    for (lo, left, left_sign), (hi, right, right_sign) in zip(checks, checks[1:]):
        if left_sign * right_sign != -1:
            continue
        initial_sign_changes += 1
        while hi - lo > TARGET_WIDTH:
            width = hi - lo
            for candidate in (lo + width / 2, lo + width / 4, hi - width / 4):
                sampled = completed_sign(candidate, dottie, pairs)
                candidate_sign = sign(sampled[0])
                if candidate_sign == left_sign:
                    lo, left = candidate, sampled
                    break
                if candidate_sign == right_sign:
                    hi, right = candidate, sampled
                    break
            else:
                raise ArithmeticError("Quartet tail enclosure prevents the requested refinement")
        assert sign(left[0]) * sign(right[0]) == -1
        print(f"Certified line-zero interval ({float(lo)}, {float(hi)}), width {float(hi - lo)}")
        report(lo, left, show_contributions=True)
        report(hi, right, show_contributions=True)

    assert initial_sign_changes > 0
    print("Each certified interval contains a zero on the line. Sign changes establish existence.")


if __name__ == "__main__":
    scan_and_refine()
