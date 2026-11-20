"""Signed completed values for the base field, divided by positive gamma moduli.

Python 3 + python-flint 0.9.0. Write the JSON precision record to stdout.
Definitions and smoothed functional-equation error proof are in gaussian-endpoints.md.
"""
import json
from math import ceil

from flint import acb, arb, ctx
from gaussian_inputs import height


def beta_hardy(t, b):
    w = acb(arb(1)/2, t)
    z = (1+w)/2
    logqpi = (4/arb.pi()).log()
    theta = z.lgamma().imag + t*logqpi/2
    absz = abs(z)
    x = (4*absz/arb.pi()).sqrt()
    lx = x.log()
    limit = ceil(float(x)*1.01*float(arb(16).exp()**(arb(1)/b)))
    log_cut = (arb(limit)/x).log()
    power = b*b*log_cut/4
    assert power > 1 and t > 2 and absz > 12*b+1
    total = arb(0)
    for n in range(1, limit+1, 2):
        an = arb(n)
        ln = an.log()
        weight_twice = ((ln-lx)*b/2).erfc()
        term = (theta-t*ln).cos()*weight_twice/an.sqrt()
        if n % 4 == 1:
            total += term
        else:
            total -= term

    # Tail of 2*sum n^-1/2 W(n/X); erfc(y) <= exp(-y²) for y>=0.
    tail = arb(limit).sqrt()*(-power*log_cut).exp()/(power-arb(1)/2)
    v = 12*b
    assert 2*(1+v*v)/(absz-v) < arb(1)/2
    prefactor = 3*x*(arb(1)/(b*b)).exp()/(2*arb.pi())
    near = 4*(b*arb.pi().sqrt()+b*b)/(absz-v)
    far = b*b*(1+arb(3)/v)*arb(-144).exp()
    gamma_error = prefactor*(near+far)
    return total + arb(0,(tail+gamma_error).upper()), dict(
        smoothing=b, terms_through=limit, smoothing_error=str(gamma_error),
        omitted_series_error=str(tail))


def main():
    ctx.prec=144
    center=height()
    rows=[]
    for offset in (-1,1):
        t=center+arb(offset)/16
        w=acb(arb(1)/2,t)
        theta=(w/2).lgamma().imag - t*arb.pi().log()/2
        z_value=acb(0,theta).exp()*w.zeta()
        assert z_value.imag.contains(0)
        beta, record=beta_hardy(t,16)
        value=z_value.real*beta
        sign=1 if value>0 else -1 if value<0 else 0
        rows.append(dict(offset=f"{offset}/16", t=str(t), zeta_hardy=str(z_value.real),
                         beta_hardy=str(beta), base_hardy_product=str(value),
                         base_sign=sign, beta_verifier=record))
    print(json.dumps(dict(precision_bits=ctx.prec, phase="product of positive-modulus normalized completed zeta and beta", rows=rows),indent=2))


if __name__ == "__main__":
    main()
