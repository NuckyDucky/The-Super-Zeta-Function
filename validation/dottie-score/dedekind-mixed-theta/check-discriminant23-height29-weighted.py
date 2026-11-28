"""Enclose the weighted discriminant -23 Dedekind circle at height 29."""

import argparse
import hashlib
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path

from flint import acb, acb_poly, arb, ctx


HEIGHT = 29
TERMS = 112
LOG_CUTOFF = 5
FOURIER_SAMPLES = 128
MODEL_DEGREE = 112
MODEL_DENOMINATOR = 2**288
WEIGHT_DEGREE = 48
MESH_PER_QUARTER = 1048576
I = acb(0, 1)


def coeffs(limit):
    # Q >= (x*x+y*y)/2 for both forms. Every lattice point of norm <= limit is included.
    width = isqrt(2 * limit)
    principal = [0] * (limit + 1)
    other = [0] * (limit + 1)
    for y in range(-width, width + 1):
        for x in range(-width, width + 1):
            a, b = x*x + x*y + 6*y*y, 2*x*x + x*y + 3*y*y
            if 0 < a <= limit:
                principal[a] += 1
            if 0 < b <= limit:
                other[b] += 1
    return (acb_poly([p+2*q for p, q in zip(principal, other)]),
            acb_poly([p-q for p, q in zip(principal, other)]))


def theta_tail(alpha):
    # A form has at most 16*n points of norm n, since (2*sqrt(2*n)+1)^2 <= 16*n.
    # Thus both coefficient sequences have absolute value <= 48*n.
    # In -5/4 <= Re(w) <= 11/4, the folded t-weight has norm <= t^2 for t >= 1.
    x = (-alpha).exp()
    omitted = 240 * x**(TERMS + 1) / (1 - x)
    cutoff = arb(LOG_CUTOFF).exp()
    q = (-alpha * cutoff).exp()
    beyond = 48 * (cutoff**2 + 2*cutoff + 2) * q / (1 - q)
    return (omitted + beyond).upper()


def class_product(w, alpha, polynomials, allowance):
    # The integral is in u=log(t). Its integrand is entire in u.
    def fold(poly):
        def integrand(u, _analytic):
            q = (-alpha * u.exp()).exp()
            return poly(q) * ((w*u).exp() + ((1-w)*u).exp()) / 2

        result = acb.integral(integrand, 0, LOG_CUTOFF, abs_tol=arb('1e-66'), eval_limit=200000)
        if not result.is_finite():
            raise ArithmeticError("Non-finite theta quadrature enclosure")
        return result + acb(arb(0, allowance), arb(0, allowance))

    summed, differenced = (fold(poly) for poly in polynomials)
    return 8 * (summed - arb(3)/2 / (w*(1-w))) * differenced**2


def enclose_model(center, alpha, forms, allowance, circle_data_path=None):
    # Re(w) is in [-5/4,11/4] on the Cauchy disk. The t^2 bound gives
    # <= 240 sum(exp(-n), n>=1) < 240 for either integral. The pole term
    # is < 1 as |Im(w)| >= 27, so |8*A*C^2| < 2^30 there.
    outer = arb(2)
    fourier = arb(1)/2
    weight_disk = arb(63)/256
    if not (weight_disk < fourier < outer and center.imag - outer >= 27):
        raise ArithmeticError("Cauchy disk failed the analytic bound")
    roots = [(2 * arb.pi() * I * k / FOURIER_SAMPLES).exp() for k in range(FOURIER_SAMPLES)]
    readings = [class_product(center + fourier * root, alpha, forms, allowance) for root in roots]
    coefficients = [sum((readings[j] * roots[(-j*k) % FOURIER_SAMPLES]
                         for j in range(FOURIER_SAMPLES)), acb(0))/FOURIER_SAMPLES
                    for k in range(MODEL_DEGREE + 1)]
    retained = [rational_midpoint(z, MODEL_DENOMINATOR) for z in coefficients]
    if circle_data_path is not None:
        samples = [rational_midpoint(z, MODEL_DENOMINATOR) for z in readings]
        sample_error = max(abs(a-b).upper() for a, b in zip(readings, samples))
        rounded_dft = [sum((samples[j] * roots[(-j*k) % FOURIER_SAMPLES]
                            for j in range(FOURIER_SAMPLES)), acb(0))/FOURIER_SAMPLES
                       for k in range(MODEL_DEGREE + 1)]
        rounding_error = max(abs(a-b).upper() for a, b in zip(rounded_dft, retained))
        limit = arb(1) / 10**72
        if not (sample_error < limit and rounding_error < limit):
            raise ArithmeticError("Sample or coefficient roundoff exceeds the Lean input")
        dataset = {
            "denominator": str(MODEL_DENOMINATOR),
            "samples": [[str((component*MODEL_DENOMINATOR).unique_fmpz())
                         for component in (z.real, z.imag)] for z in samples],
            "sampleErrorUpper": sample_error.str(12),
            "coefficientErrorUpper": rounding_error.str(12),
        }
        if any("None" in pair for pair in dataset["samples"]):
            raise ArithmeticError("Nonexact rational circle sample")
        sample_data = {"denominator": dataset["denominator"], "samples": dataset["samples"]}
        encoded = json.dumps(sample_data, sort_keys=True, separators=(",", ":")).encode()
        dataset["rationalSampleSha256"] = hashlib.sha256(encoded).hexdigest()
        circle_data_path.write_text(json.dumps(dataset, indent=2) + "\n", encoding="utf-8")
    ratio = weight_disk/outer
    alias = (fourier/outer)**FOURIER_SAMPLES
    interpolation = 2**30/(1-ratio) * (ratio**(MODEL_DEGREE+1) + alias/(1-alias))
    rounding = polynomial_bound([z-mid for z, mid in zip(coefficients, retained)], weight_disk/fourier)
    return retained, (interpolation+rounding).upper(), fourier


def rational_midpoint(z, denominator):
    def rounded(value):
        numerator = (value.mid() * denominator + arb(1)/2).floor().unique_fmpz()
        if numerator is None:
            raise ArithmeticError("Could not pick a rational midpoint")
        return arb(numerator)/denominator
    return acb(rounded(z.real), rounded(z.imag))


def polynomial_bound(coefficients, radius, use_absolute_parts=False):
    def size(z):
        if use_absolute_parts:
            return abs(z.real)+abs(z.imag)
        return abs(z)
    return sum((size(a)*radius**k for k, a in enumerate(coefficients)), arb(0)).upper()


def inverse_weight(model, degree):
    if model[0].contains(0):
        raise ArithmeticError("The model constant is zero")
    # Form the Taylor coefficients of -i/P, then round the finished coefficients.
    # The later residual test certifies the rounded polynomial.
    values = [-I/model[0]]
    for k in range(1, degree+1):
        total = sum((model[j]*values[k-j] for j in range(1, k+1)), acb(0))
        values.append(-total/model[0])
    return [rational_midpoint(z, 1) for z in values]


def encode_coefficients(coefficients, denominator):
    # The Fourier polynomial uses (w-c)/(1/2). Export coefficients of (w-c).
    result = []
    for k, z in enumerate(coefficients):
        scale = 2**k * denominator
        parts = [(scale * v).unique_fmpz() for v in (z.real, z.imag)]
        if None in parts:
            raise ArithmeticError("Nonexact rational polynomial coefficient")
        result.append([str(part) for part in parts])
    return {"denominator": str(denominator), "numerators": result}


def check_rational_polynomial_bounds(witness):
    """Check the model norm and residual using integer square-root ceilings."""
    model = [tuple(map(int, pair)) for pair in witness["model"]["numerators"]]
    weight = [tuple(map(int, pair)) for pair in witness["weight"]["numerators"]]
    denominator = int(witness["model"]["denominator"])
    residual = [[0, 0] for _ in range(len(model) + len(weight) - 1)]
    for k, (a, b) in enumerate(weight):
        for j, (c, d) in enumerate(model):
            residual[k+j][0] += a*c - b*d
            residual[k+j][1] += a*d + b*c
    residual[0][1] += denominator

    def coefficient_norm_ceiling(re, im):
        squared = re*re + im*im
        root = isqrt(squared)
        return Fraction(root + (root*root < squared), denominator)

    def bound(coefficients, radius):
        return sum(coefficient_norm_ceiling(re, im)*radius**k
                   for k, (re, im) in enumerate(coefficients))

    model_ceiling = bound(model, Fraction(63, 256))
    if not model_ceiling + Fraction(2, 10**68) <= Fraction(4, 10**56):
        raise ArithmeticError("The exact model norm and the uniform error exceed the outer bound")
    if not bound(residual, Fraction(31, 128)) <= Fraction(32, 125):
        raise ArithmeticError("The exact weighted polynomial exceeds the residual bound")


def check_disk(precision, witness_path, circle_data_path=None):
    ctx.prec = precision
    alpha = 2 * arb.pi() / arb(23).sqrt()
    if not alpha > 1:
        raise ArithmeticError("Theta scale below the integral-tail premise")
    allowance = theta_tail(alpha)
    center = acb(arb(3)/4, HEIGHT)
    model, model_error, fourier = enclose_model(center, alpha, coeffs(TERMS), allowance, circle_data_path)
    r = arb(31)/128
    rho = arb(63)/256
    field_bound = (polynomial_bound(model, rho/fourier) + model_error).upper()
    weight = inverse_weight(model, WEIGHT_DEGREE)
    residual = polynomial_bound(acb_poly(weight)*acb_poly(model) + I, r/fourier)
    coefficient_bound = polynomial_bound(weight, rho/fourier, use_absolute_parts=True)
    # |Re(W)| + |Im(W)| <= 2*|W| <= 2*coefficient_bound.
    weighted_error = (2 * coefficient_bound * model_error).upper()
    mesh_allowance = (124*coefficient_bound*field_bound/MESH_PER_QUARTER).upper()
    margin = (1 - residual - weighted_error - mesh_allowance).lower()
    # Outward rational bounds used as premises of the height-29 Lean theorem.
    if not (coefficient_bound < 3*10**58 and field_bound < arb(4)/10**56 and
            residual < arb(32)/125 and model_error < arb(2)/10**68 and margin > arb(3)/5):
        raise ArithmeticError("The rational budgets for the fixed Lean check were not certified")
    witness = {"model": encode_coefficients(model, MODEL_DENOMINATOR),
               "weight": encode_coefficients(weight, 1)}
    check_rational_polynomial_bounds(witness)
    serialized = json.dumps(witness, sort_keys=True, separators=(",", ":"))
    if witness_path is not None:
        witness_path.write_text(json.dumps(witness, indent=2) + "\n", encoding="utf-8")
    return {"center": ["3/4", HEIGHT], "measuringRadius": "31/128", "outerRadius": "63/256",
            "precisionBits": ctx.prec, "thetaErrorUpper": allowance.str(12),
            "fourierSamples": FOURIER_SAMPLES, "modelDegree": MODEL_DEGREE,
            "modelErrorUpper": model_error.str(12), "outerFieldNormUpper": field_bound.str(12),
            "weightDegree": WEIGHT_DEGREE, "weightCoefficientBoundUpper": coefficient_bound.str(12),
            "weightedModelResidualUpper": residual.str(12),
            "weightedSampleErrorUpper": weighted_error.str(12), "meshPerQuarter": MESH_PER_QUARTER,
            "meshAllowanceUpper": mesh_allowance.str(12), "wholeCircleMarginLower": margin.str(12),
            "rationalPolynomialBoundsPassed": True,
            "rationalWitnessSha256": hashlib.sha256(serialized.encode()).hexdigest()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=288)
    parser.add_argument("--witness", type=Path, help="Write the exact rational polynomials to JSON")
    parser.add_argument("--circle-data", type=Path, help="Write the rational circle samples and bounds")
    options = parser.parse_args()
    print(json.dumps(check_disk(options.precision, options.witness, options.circle_data), indent=2))
