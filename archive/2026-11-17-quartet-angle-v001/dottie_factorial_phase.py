"""Compare the exact central-binomial phase with the quartet-corrected phase."""
from functools import lru_cache
from dottie_grid_nomination import centers
from verify_binomial_normalization import arb, ctx, isolate


@lru_cache(maxsize=None)
def radial_log(n):
    radius, _, _ = isolate(n)
    return (radius / (2 * arb.pi() * n)).log()


def increments(n):
    factorial = (arb(1) / (4*n*(n+1))).log1p()
    return factorial, factorial + radial_log(n+1) - radial_log(n)


if __name__ == "__main__":
    ctx.prec = 384
    delta, height, _, _ = centers()
    index = ((-(-delta).expm1()).rsqrt() - 1) / 2
    lower = int(index.floor().unique_fmpz())
    print("First factorial opposition, continuous level", index.str(27))
    print("Differences from pi, in radians, at first Dottie height:")
    def excess(n):
        a, b = increments(n)
        return height*a/2-arb.pi(), height*b/2-arb.pi()
    lo, hi = lower-512, lower+512
    assert excess(lo)[1] > 0 and excess(hi)[1] < 0
    while hi-lo > 1:
        mid = (lo+hi)//2
        val = excess(mid)[1]
        if val > 0:
            lo = mid
        else:
            assert val < 0
            hi = mid
    for n in sorted({lower, lower+1, lo, hi}):
        a, b = excess(n)
        print(n, "factorial", a.str(16), "full", b.str(16))
    assert excess(lower)[0] > 0 and excess(lower+1)[0] < 0
