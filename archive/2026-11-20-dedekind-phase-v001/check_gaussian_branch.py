"""Integer checks for the branch quartic over the Gaussian integers (Python 3)."""

from math import isqrt


def square_coefficients(values):
    result = [0] * (2 * len(values) - 1)
    for i, a in enumerate(values):
        for j, b in enumerate(values):
            result[i + j] += a * b
    return result


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def multiply_gaussian(left, right):
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def main():
    if not __debug__:
        raise RuntimeError("The checker requires enabled assertions.")
    # Coefficients are in ascending order, starting with the constant term.
    numerator = (-659, -183, 465)
    denominator = (-936, 396, 155)
    a = [n - d for n, d in zip(numerator, denominator)]
    b = [2 * n for n in numerator]
    branch = [u + v for u, v in zip(square_coefficients(a), square_coefficients(b))]
    assert branch == [1813853, 644010, -1810543, -1039740, 961000]
    assert a[1]**2 - 4 * a[2] * a[0] == -8239
    assert numerator[1]**2 - 4 * numerator[2] * numerator[0] > 0
    constant, linear, quadratic = zip(a, b)
    square = multiply_gaussian(linear, linear)
    product = multiply_gaussian(quadratic, constant)
    real, imag = (u - 4 * v for u, v in zip(square, product))
    norm = real**2 + imag**2
    assert (real, imag) == (-5045155, 1027708)
    assert norm == 26509772707289 and norm % 3 == 2
    assert isqrt(norm)**2 < norm

    expected = {
        13: ([5, 8], [6, 11], [-1, -1], []),
        37: ([6, 31], [30, 4], [1, 1], [10, 12, 24, 25]),
        73: ([27, 46], [34, 8], [-1, 1], [30, 56]),
    }
    print(f"Gaussian discriminant = {real} + {imag}i; norm = {norm}")
    for p, recorded in expected.items():
        assert norm % p != 0 and branch[-1] % p != 0 and p % 12 == 1
        i_values = [r for r in range(p) if (r * r + 1) % p == 0]
        delta = [(real + imag * r) % p for r in i_values]
        character = [1 if pow(x, (p - 1) // 2, p) == 1 else -1 for x in delta]
        roots = [x for x in range(p) if evaluate(branch, x) % p == 0]
        assert (i_values, delta, character, roots) == recorded
        if p == 73:
            assert 3**2 + 8**2 == p
            assert (3 + 8*i_values[0]) % p == (3 - 8*i_values[1]) % p == 0
        # Check by direct enumeration on the two Gaussian quadratic copies.
        for r, sign in zip(i_values, character):
            factor = [(u + r * v) % p for u, v in zip(a, b)]
            assert factor[-1] != 0
            root_count = sum(evaluate(factor, x) % p == 0 for x in range(p))
            assert root_count == 1 + sign
        print(f"p={p}: i={i_values}, delta={delta}, signs={character}, quartic roots={roots}")


if __name__ == "__main__":
    main()
