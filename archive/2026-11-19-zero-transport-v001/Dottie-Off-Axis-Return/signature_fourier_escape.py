"""Certify uniform Rouché constants for the symmetric Hurwitz Fourier sum.

DLMF 25.11.9 writes zeta(w,b)+zeta(w,1-b) as
4 Gamma(1-w) (2 pi)^(w-1) sin(pi w/2) times S=sum cos(2 pi n b) n^(w-1).
For b approaching 1/4 from below set c=cos(2 pi b), d=1-2c^2,
A=log_2(d/c), and w*=1-A+2 pi i k/log(2). Here k is any nonzero integer.
For 0<c<=.05, put r=8c, s=A-r. On the disk, Re(w-1)<=-s.
The first two terms of S/c are 1-2^(w-w*). On its circle their modulus
is at least 2 r log(2) - expm1(r log(2)) by the power series remainder.
Dividing by c is bounded below by its value at c=.05, since expm1(x)/x
increases. The model zero is simple and its nearest translates lie at
distance 2 pi/log(2)>r. The gamma factors have no zero in these nonreal disks.

Odd harmonic coefficients have magnitude <=n c by |sin(n u)|<=n|sin u|
with u=arcsin c. Even coefficients have magnitude <=1. Separately bounding
each decreasing progression by its first term plus its tail integral gives
 |S/c -(1-2^(w-w*))| <= 3^(1-s)(1+3/(2(s-2))) + 4^(-s)(1+2/(s-1))/c.
Divide again by c. After writing p=log_2(3), the separate coefficients are
3^(1+r)c^(p-1)d^(-p) and 4^r/d^2, respectively. All positive factors
increase with c (s decreases). Thus substituting c=.05 yields uniform
upper and lower bounds certified below. Rouché gives exactly one simple
zero in the disk for each b. Analytic dependence plus strict isolation
glues these zeros as b varies. Re w tends to -infinity.

Write h=w-w*, eta=exp(2 pi i k log_2(3)). The disk proves h=O(c).
In S/c the fourth term is c+O(c^2). Terms three and six together are
-4 eta c^p+O(c^(p+1)): cos(3 arccos c)=-3c+O(c^3), cos(6 arccos c)
=-1+O(c^2), and exp(2 pi i k log_2(6))=eta. Integral comparison starting
at n=5 for odd n and n=8 for even n gives O(c^log_2(5))+O(c^2).
As 1-2^h=-h log(2)+O(c^2), the zero satisfies
 h = (c - 4 eta c^p)/log(2) + O(c^2).
The optional residuals below illustrate the asymptotic at k=2.
"""
import argparse
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def input_geometry(c,k):
    d = 1 - 2*c*c
    log2 = arb(2).log()
    A = (d/c).log()/log2
    return acb(1-A,2*k*arb.pi()/log2), c.acos()/(2*arb.pi())


def uniform_constants():
    c = arb(1)/20
    d = 1-2*c*c
    log2 = arb(2).log()
    r = 8*c
    s = (d/c).log()/log2-r
    assert s>3 and r<2*arb.pi()/log2
    odd = arb(3)**(1-s)*(1+3/(2*(s-2)))/c
    even = arb(4)**(-s)*(1+2/(s-1))/c**2
    model = (2*r*log2-(r*log2).expm1())/c
    assert odd+even < arb('4.43') and model > arb('4.65')
    return {key:x.str(28) for key,x in
            [('max_tail_divided_by_c',odd+even),('min_model_divided_by_c',model),
             ('c_max',c),('s_min',s),('max_Rouche_ratio',(odd+even)/model)]}


def illustration(c,k):
    # At a fixed rational c, solve the original Hurwitz sum. Certify a simple
    # zero in a fine disk by a second affine Rouché comparison on its boundary.
    center,b = input_geometry(c,k)
    z = center.mid()
    def jet(w):
        t = acb_series([w,1],2)
        return t.zeta(b) + t.zeta(1-b)
    for _ in range(7):
        y = jet(z)
        z = (z-y[0]/y[1]).mid()
    eps = arb('1e-45')
    df = jet(z)[1].mid()
    disk = z+acb(arb(0,eps),arb(0,eps))
    ratio = abs(jet(z)[0]/df)/eps + abs(jet(disk)[1]/df-1)
    assert ratio<1 and abs(center-z)+eps<8*c
    log2=arb(2).log()
    p=arb(3).log()/log2
    eta=acb(0,2*k*arb.pi()*p).exp()
    error=disk-center-(c-4*eta*c**p)/log2
    return {'c':c.str(16),'zero_real':disk.real.str(24),'zero_imag':disk.imag.str(24),
            'asymptotic_residual_divided_by_c_squared':abs(error/c**2).str(20)}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    ctx.prec=384
    ctx.cap=2
    result={'bits':ctx.prec,'uniform':uniform_constants(),
            'k=2_examples':[illustration(arb(1)/n,2) for n in (100,1000,10000,100000)]}
    output=json.dumps(result,indent=2)
    print(output)
    if args.out:
        args.out.write_text(output+'\n',encoding='utf-8')
