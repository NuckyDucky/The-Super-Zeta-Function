"""Reconstruct a Riemann zero with ordered return jets and a finite coupling recursion.

Run 'python quartet_return_recursion.py predict prediction.json' with python-flint,
then 'python quartet_return_recursion.py check prediction.json'. The first invocation
only uses elementary complex arithmetic, gamma, real root isolation, and quadrature.
It never evaluates Riemann zeta. A fresh output file protects the original prediction.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from verify_quartet_response_zero import acb, arb, ctx, paired_tail, quartet_input


LEVELS = 2048
ORDER = 72
START = 31
STOP = 40
STEPS = 16


def rational(value):
    q = Fraction(value)
    return arb(q.numerator) / q.denominator


def rooted_jet(k):
    other = 2-k
    cubic = (other**2 + 3*k*other + k**2)/6
    quartic = (other**3 + 7*k*other**2 + 6*k**2*other + k**3)/24
    return cubic, quartic


def read_return(u, sign, reference_weight):
    alpha = sign*acb(0,1)*(-acb(0,1)*u).exp()
    k = 2*alpha/(1+alpha)
    cubic, forward = rooted_jet(k)
    _, reversed_origin = rooted_jet(2-k)
    weight = (3*cubic-2)/2
    signed_u = 3*acb(0,1)*(forward-reversed_origin)/(2*weight**2)
    assert signed_u.overlaps(u) and weight.overlaps(reference_weight)
    assert signed_u.real > 0
    return signed_u.log(), weight


def original_jets():
    dottie, pairs = quartet_input(LEVELS)
    real_mode = read_return(acb(dottie), 1, 1/(2*(1+dottie.sin())))
    modes = []
    for n, (log_u, reference_weight) in enumerate(pairs, 1):
        root, weight = read_return(log_u.exp(), (-1)**n, reference_weight)
        modes.extend(((root,weight),(root.conjugate(),weight.conjugate())))
    return [real_mode,*modes]


def response_terms(w, order):
    # Coupling derivatives 2 through order, collapsed by the finite geometric sum.
    # The substitution v=exp(2y) leaves twice the following integrand.
    def integrand(y, analytic):
        x = y.exp()
        c = x.cosh()**2
        q = x*x/(c+x*x)
        return ((4-w)*y).exp()*(1-q**(order-1))/(c*(c+x*x))

    cuts = [-35,-20,-12,-8,-4,0,1,2,3,4]
    integral = sum(acb.integral(integrand,a,b,abs_tol=arb("1e-36"))
                   for a,b in zip(cuts,cuts[1:]))
    # On the real line the finite sum starting at q^2 is in [0,h^2/(1+h)].
    left = (-35*(4-w.real)).exp()/(4-w.real)
    x = arb(4).exp()
    right = 16*(-4*x).exp()*(x**3/4+3*x**2/16+3*x/32+arb(3)/128)
    tail = arb(0,left+right)
    s = w/2
    factor = s*(arb.pi()*s).sin()/arb.pi()
    # A coarse rational upper bound on sup q. x*tanh(x)=1 below 6/5,
    # hence sup q = 1-1/x^2 < 11/36. This inequality is certified here.
    trial = arb(6)/5
    assert trial*trial.tanh() > 1
    ratio = arb(11)/36
    kernel_error = abs(factor)*ratio**order*(1/s.real+1/(1-s.real))
    ball = arb(0,kernel_error)
    return 2*factor*(integral+acb(tail,tail))+acb(ball,ball), kernel_error


def completed(height, modes):
    w = acb(arb(1)/2,rational(height))
    root_sum = sum(weight*(-w*log_u).exp() for log_u,weight in modes)
    tail = arb(0,paired_tail(w,LEVELS))
    first = w*(root_sum+acb(tail,tail))
    rest, error = response_terms(w,ORDER)
    phase = ((w*arb.pi().log()/2).exp()*(w/2).gamma()
             /(2*((w*arb(2).log()).exp()-1)))
    value = (first+rest)*phase/abs(phase)
    assert value.imag.contains(0) and value.real.is_finite()
    return value.real,error


def prediction():
    modes = original_jets()
    print(f"Recovered {len(modes)} sign-quotient modes from rooted cubic and quartic jets.",flush=True)
    lo = Fraction(START)
    left,_ = completed(lo,modes)
    for n in range(START+1,STOP+1):
        hi = Fraction(n)
        right,_ = completed(hi,modes)
        if left*right < 0:
            break
        assert left*right > 0
        lo,left = hi,right
    else:
        raise ArithmeticError("No certified crossing in the declared scan.")
    print(f"Initial crossing ({lo}, {hi})",flush=True)
    # A non-certified midpoint can arise close to a zero. Keep certified endpoints.
    for _ in range(STEPS):
        for q in (Fraction(1,2),Fraction(1,4),Fraction(3,4)):
            t = lo+q*(hi-lo)
            mid,_ = completed(t,modes)
            if mid*left > 0:
                lo,left = t,mid
                break
            if mid*right > 0:
                hi,right = t,mid
                break
        else:
            break
    assert left*right < 0
    return {"precision_bits":ctx.prec,"quartets":LEVELS,"coupling_order":ORDER,
            "search":[START,STOP],"height_lo":str(lo),"height_hi":str(hi),
            "response_at_lower_height":[left.lower().str(14),left.upper().str(14)],
            "response_at_upper_height":[right.lower().str(14),right.upper().str(14)],
            "height_decimal_approx":[float(lo),float(hi)],
            "response_tail_upper":completed(hi,modes)[1].upper().str(12)}


def independent_check(record):
    def hardy(t):
        w = acb(arb(1)/2,t)
        theta = (w/2).lgamma().imag-t*arb.pi().log()/2
        return (acb(0,theta).exp()*w.zeta()).real
    a,b = [rational(record[k]) for k in ("height_lo","height_hi")]
    ha,hb = hardy(a),hardy(b)
    assert ha*hb < 0
    print("Independent Hardy endpoints",ha.str(14),hb.str(14))
    for _ in range(48):
        t = (a+b)/2
        ht = hardy(t)
        if ha*ht < 0:
            b,hb = t,ht
        else:
            assert hb*ht < 0
            a,ha = t,ht
    print("Independent zero enclosure",a.union(b).str(28))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["predict","check"])
    parser.add_argument("record",type=Path)
    args = parser.parse_args()
    ctx.prec = 192
    if args.mode == "predict":
        record = prediction()
        with args.record.open("x",encoding="utf-8",newline="\n") as out:
            out.write(json.dumps(record,indent=2)+"\n")
        print(json.dumps(record,indent=2))
    else:
        print("Checking prediction SHA-256",hashlib.sha256(args.record.read_bytes()).hexdigest())
        independent_check(json.loads(args.record.read_text(encoding="utf-8")))
