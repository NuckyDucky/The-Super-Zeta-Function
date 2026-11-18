"""Directed zeta charts for quarter-height rectangles, using python-flint 0.9."""
from fractions import Fraction
from flint import acb, acb_poly, arb, ctx


def ball(q):
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def harmonic_height(k):
    """Exact-decimal frozen Dottie-clock convention."""
    x = ball("4.749479070945369e-8")
    y = ball("0.509892982511772")
    return k * 2 * arb.pi() / (160 * ((x/y)**2).log1p())


def full_chart(H):
    """Return a complex interval evaluator for beta + i*(H+y), plus truncation error."""
    if ctx.prec < 160:
        raise ValueError("Use at least 160 bits")
    N = 192
    R, r, a = map(ball, ("9/10", "103/200", "261/500"))
    half = ball("1/2")
    assert (half**2 + ball("1/8")**2).sqrt() < a < R
    # Euler-Maclaurin at n=1, through B_2, bounds |zeta| on this
    # disk. Re w >= -0.4; |B_2({t})| <= 1/6 in the integral.
    M = (H+3)**2
    assert H>10 and 1+half+(H+3)/12+M/(12*ball("3/5")) < M
    roots = [acb(0, 2*arb.pi()*j/N).exp() for j in range(N)]
    center = acb(half, H)
    samples = [(center+r*z).zeta() for z in roots]
    poly = acb_poly([sum(samples[j]*roots[(-j*k)%N] for j in range(N))/N
                     for k in range(N)])
    # Cauchy plus DFT aliasing, for |w-center| <= a.
    error = M*R/(R-a)*(r**N+a**N)/(R**N-r**N)
    assert error < arb("1e-15")
    noise = acb(arb(0, error), arb(0, error))
    shifted = {}
    def evaluate(beta, y):
        v = acb(beta-half, y)
        if not abs(v) < a:
            raise ValueError("Requested interval falls outside chart")
        key = tuple(round(float(component.mid())*8) for component in (v.real, v.imag))
        origin = acb(arb(key[0])/8, arb(key[1])/8)
        if key not in shifted:
            shifted[key] = poly(acb_poly([origin/r, 1]))
        return shifted[key]((v-origin)/r)+noise
    return evaluate, error


def winding(evaluate, beta_pair, y_pair):
    x0,x1 = map(Fraction,beta_pair)
    y0,y1 = map(Fraction,y_pair)
    corners = [(x0,y0),(x1,y0),(x1,y1),(x0,y1),(x0,y0)]
    segments = 0
    total = arb(0)
    samples = {}
    def point(p):
        if p not in samples:
            samples[p] = evaluate(ball(p[0]),ball(p[1]))
        return samples[p]
    def follow(a,b,depth):
        nonlocal total, segments
        image = evaluate(ball(a[0]).union(ball(b[0])), ball(a[1]).union(ball(b[1])))
        if not image.contains(0):
            # A convex interval image avoiding the origin lies in an open
            # half-plane through the origin; its net change is the principal angle.
            angle = (point(b)/point(a)).arg()
            if angle.is_finite() and abs(angle) < arb.pi():
                total += angle
                segments += 1
                return
        if depth >= 23:
            raise ArithmeticError("Unresolved contour segment")
        midpoint = tuple((v+w)/2 for v,w in zip(a,b))
        follow(a, midpoint, depth+1)
        follow(midpoint, b, depth+1)
    for a,b in zip(corners,corners[1:]):
        follow(a,b,0)
    integer = (total/(2*arb.pi())).unique_fmpz()
    if integer is None or integer < 0:
        raise ArithmeticError("Unresolved winding number")
    return {"count": int(integer), "certified_segments": segments}
