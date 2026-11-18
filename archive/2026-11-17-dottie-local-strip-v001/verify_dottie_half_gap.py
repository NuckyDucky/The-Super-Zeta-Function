"""Fixed-height horizontal slice, with python-flint ball certificates."""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "deps"))
from flint import acb, acb_poly, arb, ctx


def ball(q):
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def check_two_thirds(height, evaluate):
    half, two_thirds = ball("1/2"), ball("2/3")
    center_magnitude = abs(acb(half, height).zeta())
    lo, hi = Fraction("0.54"), Fraction("0.545")
    for _ in range(32):
        mid = (lo + hi)/2
        residual = abs(evaluate(ball(mid))) - two_thirds*center_magnitude
        if residual > 0:
            lo = mid
        else:
            assert residual < 0
            hi = mid
    for beta, sign in [(lo, 1), (hi, -1)]:
        residual = abs(acb(ball(beta), height).zeta()) - two_thirds*center_magnitude
        assert sign*residual > 0
    print("center-normalized zeta crosses 2/3 at beta", ball(lo).union(ball(hi)).str(16))
    print("zeta magnitude at crossing", (two_thirds*center_magnitude).str(19))

    # xi(w) = A(w) zeta(w). The logarithmic derivative of |A| in the
    # horizontal direction gives a uniform lower bound for the scale factor.
    strip = acb(half.union(arb(1)), height)
    slope = (1/strip + 1/(strip-1) + (strip/2).digamma()/2 - arb.pi().log()/2).real
    assert slope > 13
    pending = [(Fraction(1,2), Fraction(1))]
    pieces = 0
    while pending:
        lo, hi = pending.pop()
        domain = ball(lo).union(ball(hi))
        scale_lower = (13*(ball(lo)-half)).exp()
        if scale_lower*abs(evaluate(domain)) > two_thirds*center_magnitude:
            pieces += 1
        else:
            assert hi-lo > Fraction(1,2**30)
            mid = (lo+hi)/2
            pending.extend([(lo,mid),(mid,hi)])
    print("center-normalized |xi| exceeds 2/3 on [1/2,1], boxes", pieces)


def solve():
    ctx.prec = 192
    ratio = ball("4.749479070945369e-8") / ball(".509892982511772")
    height = 2 * arb.pi() / (160 * (ratio**2).log1p())
    center, radius = ball("3/4"), ball("1/4")
    count = 80
    roots = [acb(0, 2 * arb.pi() * k / count).exp() for k in range(count)]
    values = [(acb(center, height) + radius*z).zeta() for z in roots]
    coeff = [sum(v * roots[-j*k % count] for j, v in enumerate(values))/count
             for k in range(count)]
    # On the unit disk about 3/4+iT, Euler--Maclaurin with periodic B2
    # bounds |zeta| by (T+4)^2 (Re w >= -1/4). For degree indices < N,
    # the circular DFT aliases later coefficients of the Taylor series.
    # Their geometric sum plus the Taylor tail give this error on |v|<=a.
    a = ball("0.26")
    err = (height+4)**2 * (radius**count+a**count)/((1-a)*(1-radius**count))
    assert err < ball("1e-19")
    poly = acb_poly(coeff)
    shifted = {}

    def evaluate(beta):
        t = (beta-center)/radius
        idx = round(16*float(t.mid()))
        origin = arb(idx)/16
        if idx not in shifted:
            shifted[idx] = poly(acb_poly([origin,1]))
        return shifted[idx](t-origin) + acb(arb(0,err),arb(0,err))

    if '--two-thirds' in sys.argv:
        check_two_thirds(height, evaluate)
    # Every point of [1/2,1] has |beta-center| <= 1/4.
    threshold = ball("0.5005")
    count_boxes = 0
    todo = [(Fraction(1,2), Fraction(1))]
    while todo:
        lo,hi = todo.pop()
        if abs(evaluate(ball(lo).union(ball(hi)))) > threshold:
            count_boxes += 1
        else:
            assert hi-lo > Fraction(1,2**32)
            mid = (lo+hi)/2
            todo.extend([(lo,mid),(mid,hi)])

    def residual(c):
        return abs(evaluate(2*ball(c))) - (4*ball(c)-1)

    lo,hi = Fraction(3,8),Fraction("0.376")
    assert residual(lo)>0 and residual(hi)<0
    for _ in range(42):
        mid=(lo+hi)/2
        val=residual(mid)
        if val>0:
            lo=mid
        else:
            assert val<0
            hi=mid
    for c,sign in [(lo,1),(hi,-1)]:
        assert sign*(abs(acb(2*ball(c),height).zeta())-(4*ball(c)-1))>0
    crossing=ball(lo).union(ball(hi))
    print('boxes',count_boxes,'lower bound',threshold.str(10))
    print('crossing',crossing.str(20),'magnitude',(4*crossing-1).str(18))
    print('selected magnitude',abs(acb(ball('3/4'),height).zeta()).str(25))
    print('local dip sample',abs(acb(ball('0.711992411664640192'),height).zeta()).str(25))
    if '--coefficients' in sys.argv:
        # |t|<=1: omitted terms are bounded by the sum of their moduli.
        n=next(j for j in range(1,count) if sum(abs(v) for v in coeff[j:])<ball('1e-13'))
        print(json.dumps([[float(z.real.mid()),float(z.imag.mid())] for z in coeff[:n]]))


if __name__=='__main__':
    solve()
