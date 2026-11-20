"""Integer coefficient checks for discriminant -23. Run with Python 3."""
import json
from math import isqrt


LIMIT = 4096
FORMS = ((1, 1, 6), (2, 1, 3), (2, -1, 3))


def norm_counts(form, limit):
    a, b, c = form
    disc = 4*a*c - b*b
    counts = [0] * (limit+1)
    bound = isqrt(4*a*limit // disc)
    for y in range(-bound, bound+1):
        radius = isqrt(4*a*limit - disc*y*y)
        for x in range(-((radius+b*y)//(2*a)), (radius-b*y)//(2*a)+1):
            n = a*x*x+b*x*y+c*y*y
            if n:
                counts[n] += 1
    assert all(v % 2 == 0 for v in counts)
    return [v//2 for v in counts]  # O_K^× = {±1}


def zeta_times(data):
    counts = [0] * len(data)
    for d in range(1, len(data)):
        for n in range(d, len(data), d):
            counts[n] += data[d]
    return counts


def cubic_coefficients(limit):
    # Dedekind's factorization theorem applies at every prime, since the
    # polynomial x³−x−1 has squarefree discriminant and hence index one.
    prime = [False, False] + [True] * (limit-1)
    coeff = [0, 1] + [0] * (limit-1)
    for p in range(2, limit+1):
        if not prime[p]:
            continue
        for m in range(p*p, limit+1, p):
            prime[m] = False
        roots = sum((x**3-x-1) % p == 0 for x in range(p))
        if p == 23:
            assert roots == 2
            degrees = [1, 1]  # a simple and a double linear factor
        else:
            degrees = {0: [3], 1: [1, 2], 3: [1, 1, 1]}[roots]
        for degree in degrees:
            norm = p**degree
            for n in range(norm, limit+1, norm):
                coeff[n] += coeff[n//norm]
    return coeff


def main():
    if not __debug__:
        raise RuntimeError('Run the checker with Python assertions enabled.')
    p0, p1, p2 = [norm_counts(form, LIMIT) for form in FORMS]
    assert p1 == p2
    quadratic = [sum(row) for row in zip(p0, p1, p2)]
    residues = {a*a % 23 for a in range(1, 23)}
    # Quadratic reciprocity gives χ_{-23}(d)=(d/23), also at 2 and 23.
    chi = [0 if d % 23 == 0 else 1 if d % 23 in residues else -1
           for d in range(LIMIT+1)]
    assert quadratic == zeta_times(chi)
    artin = [principal-nonprincipal for principal, nonprincipal in zip(p0, p1)]
    cubic = zeta_times(artin)
    assert cubic == cubic_coefficients(LIMIT)
    print(json.dumps({"discriminant": -23, "forms": FORMS, "limit_inclusive": LIMIT,
                      "quadratic_coefficients_verified": LIMIT, "cubic_coefficients_verified": LIMIT,
                      "n2_by_class": [p0[2], p1[2], p2[2]],
                      "first_principal_only_mismatch": next(n for n in range(1,LIMIT+1)
                                                            if quadratic[n] != p0[n]),
                      "cubic_artin_n1_to_n12": artin[1:13],
                      "cubic_dedekind_n1_to_n12": cubic[1:13]}, indent=2))


if __name__ == '__main__':
    main()
