"""Compare the four-tag radius 2/3 with the Dottie-slice crossing using Arb."""
from verify_dottie_half_gap import acb, arb, ball, ctx
from dottie_grid_nomination import centers


def level_number(t):
    theta = (-t / t.sinh()).acos()
    return (theta + t.cosh() * theta.sin()) / arb.pi() - ball("1/2")


def solve_level(n):
    lo, hi = arb(1), arb(12)
    assert level_number(lo) < n < level_number(hi)
    for _ in range(108):
        mid = (lo + hi) / 2
        index = level_number(mid)
        if index < n:
            lo = mid
        else:
            assert index > n
            hi = mid
    return lo.union(hi)


def main():
    ctx.prec = 224
    _, height, _, _ = centers()
    half, target = ball("1/2"), ball("2/3")
    center_mag = abs(acb(half, height).zeta())
    lo, hi = ball(".542962564820"), ball(".542962564824")
    for beta, sign in [(lo, 1), (hi, -1)]:
        assert sign * (abs(acb(beta, height).zeta()) / center_mag - target) > 0
    displacement = lo.union(hi) - half
    log_ratio = -target.log()
    index = level_number(log_ratio / displacement)
    assert 1997 < index < 1998
    print("Continuous index at the common crossing:", index.str(12))
    for n in [1, 2, 3, 1997, 1998]:
        t = solve_level(n)
        beta = half + log_ratio / t
        ratio = (-t * displacement).exp()
        if n == 1:
            assert beta < ball("7/8")
        if n == 1997:
            assert ratio > target
        if n == 1998:
            assert ratio < target
        print(n, "right address", beta.str(18), "tag ratio at crossing", ratio.str(12))


if __name__ == "__main__":
    main()
