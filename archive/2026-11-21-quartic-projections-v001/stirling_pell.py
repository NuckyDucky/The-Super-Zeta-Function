"""Reproduce the fixed squarefree-part classification and the Stirling intervals."""

from math import comb, factorial, isqrt

from flint import arb, ctx


def squarefree_part(value):
    """Return q in the unique decomposition value = q*s^2, value positive."""
    divisor = 2
    while divisor * divisor <= value:
        while value % (divisor * divisor) == 0:
            value //= divisor * divisor
        divisor += 1
    return value


def pell_index_interval(n, readings, unit):
    correction = arb(0)
    for j in range(readings):
        index = n * 2**j
        balanced = arb(comb(2 * index, index)) / arb(4)**index
        reading = -(arb.pi() * index * balanced**2).log()
        correction += reading / (4 * 2**j)
    log_stirling = (2 * arb.pi() * n).log() / 2 + n * (arb(n).log() - 1)
    log_lower = log_stirling + correction
    log_upper = log_lower + 1 / (arb(12 * n) * 4**readings)
    return tuple((bound / 2).exp().asinh() / unit.log() for bound in (log_lower, log_upper))


def main():
    ctx.prec = 192
    parts = [squarefree_part(factorial(n)) for n in range(2, 14)]
    assert parts == [2, 6, 6, 30, 5, 35, 70, 70, 7, 77, 231, 3003]
    assert [n for n, q in enumerate(parts, 2) if q == 35] == [7]
    print("Squarefree parts of n!, n = 2,...,13:", parts)

    x, y = 1, 0
    powers = []
    for _ in range(3):
        x, y = 6 * x + 35 * y, x + 6 * y
        powers.append((x, y))
    assert powers == [(6, 1), (71, 12), (846, 143)]
    assert 71**2 - 1 == 35 * 12**2 == factorial(7)
    assert factorial(9) < 846**2 - 1 == 35 * 143**2 < factorial(10)
    print("Powers 1, 2, 3 of 6 + sqrt(35):", powers)
    print("Next Pell target:", 846**2 - 1)

    lower, upper = pell_index_interval(7, 4, 6 + arb(35).sqrt())
    assert arb("1.99999061736726") < lower < 2 < upper < arb("2.00000000002494")
    print("n = 7, four readings:", lower.str(18), upper.str(18))

    # The first positive Pell solution for q=70 has y=30. Since x grows
    # strictly with y, this verifies the fundamental norm-one unit.
    assert [j for j in range(1, 31) if isqrt(1 + 70*j*j)**2 == 1 + 70*j*j] == [30]
    assert 251**2 - 70 * 30**2 == 1
    assert factorial(8) == 70 * 24**2
    lower, upper = pell_index_interval(8, 4, 251 + 30 * arb(70).sqrt())
    assert arb("0.96411381949754") < lower < upper < arb("0.96411709110408")
    print("n = 8, four readings:", lower.str(18), upper.str(18))
    first_target = 251**2 - 1
    second_real_part = 251**2 + 70 * 30**2
    second_target = second_real_part**2 - 1
    assert factorial(8) < first_target < factorial(9)
    assert second_real_part == 126001 and factorial(13) < second_target
    print("First two targets for q = 70:", first_target, second_target)


if __name__ == "__main__":
    main()
