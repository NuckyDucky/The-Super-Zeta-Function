"""Paired spectral powers for the Dottie determinant, with directed root and tail bounds."""
import argparse
import json
import math
from pathlib import Path
import platform

import flint
from flint import acb, arb, ctx, dirichlet_char

from verify_moments import decimal_enclosure


ROOT_COUNT = 1024
PRECISION = 320


def bisect_increasing(function, lo, hi, steps):
    if not function(lo) < 0 or not function(hi) > 0:
        raise ArithmeticError("Failed to bracket the root.")
    for _ in range(steps):
        mid = ((lo + hi) / 2).mid()
        value = function(mid)
        if value < 0:
            lo = mid
        elif value > 0:
            hi = mid
        else:
            raise ArithmeticError("Indeterminate sign during bisection.")
    return lo.union(hi)


def determinant_roots(count):
    """The scalar phase equation and its unique indexed root are proved in the quartet classification."""
    d = bisect_increasing(lambda t: t-t.cos(), arb(0), arb(1), 270)
    roots = []
    for n in range(1, count + 1):
        frequency = n * arb.pi()

        def difference(t):
            b = t / t.sinh()
            return t.cosh() * (1-b*b).sqrt() + b.asin() - frequency

        # A binary64 seed reduces the number of interval evaluations. Both endpoints
        # are checked with Arb; a broad rigorously tested bracket is the fallback.
        t0 = math.log(2 * math.pi * n)
        for _ in range(5):
            sh, ch = math.sinh(t0), math.cosh(t0)
            b = t0/sh
            v = math.sqrt(1-b*b)
            db = (1-t0*ch/sh)/sh
            slope = sh*v + (1-ch*b)*db/v
            t0 -= (ch*v + math.asin(b) - math.pi*n)/slope
        gap = arb(2)**-37
        lo, hi = arb(t0)-gap, arb(t0)+gap
        if not difference(lo) < 0 or not difference(hi) > 0:
            lo, hi = arb(1), arb(4*count+10)
            steps = 117
        else:
            steps = 66
        t = bisect_increasing(difference, lo, hi, steps)
        b = t/t.sinh()
        xi = t.cosh() * (1-b*b).sqrt()
        if not (n-arb(1)/2)*arb.pi() < xi or not xi < frequency:
            raise ArithmeticError(f"The real part is outside level {n}.")
        u = acb(xi, t)
        if not ((-1)**n*u.cos()-u).contains(0):
            raise ArithmeticError(f"The cosine equation failed at level {n}.")
        roots.append(u**2)
    return d, roots


def finite_box(tail):
    radius = arb(0, tail.upper())
    return acb(radius, radius)


def direct_first_square():
    """A complex contraction proof for u+cos(u)=0, independent of the scalar phase equation."""
    center = acb("2.5","1.8")
    for _ in range(7):
        center = (center-(center+center.cos())/(1-center.sin())).mid()
    radius = arb(2)**-130
    box = center + finite_box(radius)
    inverse_slope = 1/(1-center.sin())
    derivative_bound = abs(1-inverse_slope*(1-box.sin()))
    center_error = abs(inverse_slope*(center+center.cos()))
    if not center_error+radius*derivative_bound < radius:
        raise ArithmeticError("The complex cosine contraction did not map the disk inside itself.")
    if not box.real > arb.pi()/2 or not box.real < arb.pi() or not box.imag > 0:
        raise ArithmeticError("The contraction box is outside the first upper quartet.")
    return box**2


def spectral_pair(d, roots, x, y):
    z = x + y.conjugate()
    q = x - y.conjugate()
    direct = acb(d*d)**(-x) * (acb(d*d)**(-y)).conjugate()
    grouped = base = acb(d*d)**(-z)
    angular = acb(0)
    for lam in roots:
        for member in (lam, lam.conjugate()):
            direct += member**(-x) * (member**(-y)).conjugate()
        radial = acb(abs(lam))**(-z)
        psi = lam.arg()
        grouped += 2*radial*(q*psi).cos()
        base += 2*radial*(z*psi).cos()
        angular += 4*radial*(x*psi).sin()*(y.conjugate()*psi).sin()
    if not direct.overlaps(grouped) or not direct.overlaps(base+angular):
        raise ArithmeticError("Principal powers, polar form and angular correction disagree.")
    # |u_n|^2 > [pi(n-1/2)]^2. Each squared root has principal argument in (-pi,pi).
    exponent = 2*z.real
    if not exponent > 1:
        raise ArithmeticError("This full-series bound requires absolute convergence.")
    tail_scale = (len(roots)-arb(1)/2)**(1-exponent) / ((exponent-1)*arb.pi()**exponent)
    pair_tail = 2*((abs(x.imag)+abs(y.imag))*arb.pi()).exp()*tail_scale
    base_tail = 2*(abs(z.imag)*arb.pi()).exp()*tail_scale
    return direct+finite_box(pair_tail), base+finite_box(base_tail), angular+finite_box(pair_tail+base_tail)


def complex_enclosure(value, digits=8):
    return {"real": decimal_enclosure(value.real, digits), "imag": decimal_enclosure(value.imag, digits)}


def recover_angle(d, roots):
    # The triangular average has Fourier multiplier sinc(T*log(R/R_j)/2)^2.
    # Radius is supplied here. The complex argument is withheld from the inverse step.
    cutoff = 2**19
    target = abs(roots[0])
    gap = min((target/(d*d)).log().lower(), (((3*arb.pi()/2)**2)/target).log().lower())
    if not gap > 0:
        raise ArithmeticError("Failed to separate the first nonreal modulus.")
    normal_mass = d**-4 + sum(2/abs(lam)**2 for lam in roots)
    root_tail = 2 / (3*arb.pi()**4*(len(roots)-arb(1)/2)**3)
    normal_mass += arb(0, root_tail.upper())
    isolated = []
    field = []
    for eta in (0, 1):
        weight = lambda radius: (cutoff*(target/radius).log()/2).sinc()**2
        value = d**-4*weight(d*d)
        for lam in roots:
            value += 2*weight(abs(lam))*(eta*lam.arg()).cosh()/abs(lam)**2
        eta_bound = (eta*arb.pi()).cosh()
        truncation = root_tail*eta_bound*4/(cutoff*gap)**2
        finite_average = value + arb(0).union(truncation.upper())
        leakage = normal_mass*eta_bound*4/(cutoff*gap)**2
        isolated.append(finite_average - arb(0).union(leakage.upper()))
        field.append(decimal_enclosure(finite_average, 13))
    recovered = (isolated[1]/isolated[0]).acosh()
    isolated_root = roots[0].arg()
    if not recovered.contains(isolated_root):
        raise ArithmeticError("The recovered angle missed the independently isolated root angle.")
    return {"filter_half_width": cutoff, "input_radius": decimal_enclosure(target, 12),
            "frequency_gap_lower": decimal_enclosure(gap, 10)[0],
            "filtered_at_eta_0_and_1": field,
            "angle_from_two_filtered_values_radians": decimal_enclosure(recovered, 8),
            "angle_directly_from_cosine_root_radians": decimal_enclosure(isolated_root, 13)}


def raw_diagonal(d, roots, real_part, eta):
    """One complete positive reading, including the real Dottie root."""
    x = acb(real_part, arb(eta)/2)
    value = abs(acb(d*d)**(-x))**2
    for lam in roots:
        value += abs(lam**(-x))**2 + abs(lam.conjugate()**(-x))**2
    exponent = 4 * real_part
    tail = 2*(eta*arb.pi()).cosh() / (
        (exponent-1)*arb.pi()**exponent*(len(roots)-arb(1)/2)**(exponent-1))
    return value+arb(0).union(tail.upper())


def recover_from_five(readings):
    """Inputs are five full scalar values in order (16,0/1/2), (17,0/1)."""
    h0, h1, h2, k0, k1 = readings

    def first_term(delta, real_part, eta):
        # Bound every contribution starting at n=2. No mass, radius, angle
        # or position from the first quartet enters this inverse calculation.
        exponent = 4*real_part
        start = arb(3)/2
        rest = 2*((eta*arb.pi()).cosh()-1)*(arb.pi()*start)**(-exponent)*(
            1+start/(exponent-1))
        first = delta-arb(0).union(rest.upper())
        if not first > 0:
            raise ArithmeticError("The five readings did not resolve the first pair.")
        return first

    d1 = first_term(h1-h0,16,1)
    d2 = first_term(h2-h0,16,2)
    next_d1 = first_term(k1-k0,17,1)
    return (d1/next_d1).sqrt(), (d2/(2*d1)-1).acosh()


def arithmetic_covariance(u, v):
    j = u+v.conjugate()
    return 9/arb.pi()**2 * (1-acb(3)**(-3-j))*(3+j).zeta() / (1-acb(3)**(-1-j))


def observed_shifted_means(a):
    chi = dirichlet_char(3, 2)
    shift = acb(0,a)
    products = [acb(0), acb(0), acb(0)]
    record = {}
    for n, rho in enumerate(acb.zeta_zeros(1,1024),1):
        plus, minus = [3*(1+z).dirichlet_l(chi)/(arb.pi()*(1-acb(3)**(-z)))
                       for z in (rho+shift,rho-shift)]
        products[0] += abs(plus)**2
        products[1] += plus*minus.conjugate()
        products[2] += abs(minus)**2
        if n in (64,256,1024):
            record[str(n)] = {sign:complex_enclosure(value/n,8)
                              for sign,value in zip(("++","+-","--"),products,strict=True)}
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.prec = PRECISION
    d, roots = determinant_roots(ROOT_COUNT)
    a = arb.pi()/6
    cases = {}
    stored = {}
    for sx, sy, name in ((0,0,"origin"), (1,1,"++"), (1,-1,"+-"), (-1,1,"-+"), (-1,-1,"--")):
        u, v = acb(0, sx*a), acb(0, sy*a)
        value, base, defect = spectral_pair(d, roots, 1+u, 1+v)
        cases[name] = {"determinant_pair_at_real_part_1": complex_enclosure(value),
                       "angular_correction": complex_enclosure(defect),
                       "ordinary_same_index_at_real_part_2": complex_enclosure((4+u+v.conjugate()).zeta()),
                       "limiting_shifted_speed_product": complex_enclosure(arithmetic_covariance(u,v))}
        stored[name] = value
        if name == "origin" and (not base.contains(acb(10)/3) or not defect.real > 0):
            raise ArithmeticError("The second trace or the angular excess failed.")
    if not stored["++"].overlaps(stored["--"]) or not stored["++"].real > stored["origin"].real:
        raise ArithmeticError("The same-sign diagonal check failed.")
    if not stored["+-"].overlaps(stored["-+"].conjugate()) or stored["+-"].imag.contains(0):
        raise ArithmeticError("The conjugate pair failed.")
    # Also use the two already-summed ordinary zeta values as the literal inputs.
    zx, zy = acb(2,a).zeta(), acb(3,-a).zeta()
    nested, _, _ = spectral_pair(d, roots, zx, zy)
    settings = [(16,0),(16,1),(16,2),(17,0),(17,1)]
    raw = [raw_diagonal(d,roots[:32],r,eta) for r,eta in settings]
    # Pass only the outward-rounded decimal readings to the inverse.
    readings = [decimal_enclosure(value, 57) for value in raw]
    blind_radius, blind_angle = recover_from_five(
        [arb(lo).union(arb(hi)) for lo,hi in readings])
    direct = direct_first_square()
    if not direct.overlaps(roots[0]):
        raise ArithmeticError("The independent complex contraction missed the scalar root.")
    if not blind_radius.contains(abs(direct)) or not blind_angle.contains(direct.arg()):
        raise ArithmeticError("The independent determinant root disagrees with the inverse.")
    report = {"python": platform.python_version(), "python_flint": flint.__version__,
              "flint": flint.__FLINT_VERSION__, "precision_bits": PRECISION, "nonreal_pairs": ROOT_COUNT,
              "a": "pi/6 as an additive imaginary shift", "indexed_products": cases,
              "literal_zeta_value_inputs": {"x_zeta_2_plus_ia": complex_enclosure(zx),
                                             "y_zeta_3_minus_ia": complex_enclosure(zy),
                                             "Sz_E_x_y": complex_enclosure(nested)},
              "first_pair_recovery": recover_angle(d, roots),
              "finite_shifted_speed_quotient_means": observed_shifted_means(a),
              "inverse_from_five_real_values": {
                  "settings_real_part_and_eta": settings,
                  "full_readings_including_the_real_root": readings,
                  "radius_from_readings": decimal_enclosure(blind_radius, 12),
                  "angle_from_readings_radians": decimal_enclosure(blind_angle, 12),
                  "radius_directly_from_cosine_root": decimal_enclosure(abs(direct), 14),
                  "angle_directly_from_cosine_root_radians": decimal_enclosure(direct.arg(), 14)}}
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8", newline="\n")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
