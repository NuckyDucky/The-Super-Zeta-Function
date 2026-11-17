"""Independent point audit of shifted residues and Barnes coefficient integrals."""
from pathlib import Path
from fractions import Fraction
from math import factorial,comb
import json
import mpmath as mp

mp.mp.dps=90
HERE=Path(__file__).resolve().parent


def coefficients(m):
    p={1:1}
    for j in range(1,m):
        q={}
        for degree,c in p.items():
            q[degree+2]=q.get(degree+2,0)+c
            q[degree]=q.get(degree,0)-j*j*c
        p=q
    return p


def main():
    residue=[]
    for n in range(13):
        value=mp.mpf((-1)**n)/factorial(n)/(mp.sqrt(mp.pi)*mp.gamma(mp.mpf('.5')-n))
        target=mp.mpf(comb(2*n,n))/4**n/mp.pi
        error=abs(value-target)
        assert error<mp.mpf('1e-80')
        residue.append({'order':n,'normalized_B_exact':str(Fraction(comb(2*n,n),4**n)),
                        'gamma_residue_error':mp.nstr(error,20)})
    rows=[]
    for m in range(1,5):
        poly=coefficients(m)
        for n in range(1,m+8):
            actual=sum(c*n**j for j,c in poly.items())
            target=0 if n<m else factorial(2*m-1)*comb(n+m-1,2*m-1)
            assert actual==target
        for s in (mp.mpf('-.25'),mp.mpf(0),mp.mpf('.25'),mp.mpf('.75')):
            low=lambda q:8*q**int(8*m-8*s-1)/mp.cosh(q**4)**(2*m)
            high=lambda x:2*x**(2*m-2*s-1)/mp.cosh(x)**(2*m)
            integral=mp.quad(low,[0,1])+mp.quad(high,[1,4,12,40,120])
            pp=2*m-2*s
            eta=(-1)**(m+1)/mp.mpf(factorial(2*m-1))*sum(
                c*mp.altzeta(pp-j) for j,c in poly.items())
            predicted=2**(2*s+1)*mp.gamma(pp)*eta
            error=abs(integral-predicted)
            assert error<mp.mpf('1e-75')
            rows.append({'m':m,'s':str(s),'integral':mp.nstr(integral,65),
                         'Barnes_Dirichlet_reduction_error':mp.nstr(error,24),
                         'P_m_coefficients':poly})
    tails=[]
    for s,w,M in ((mp.mpc('.3','.4'),mp.mpf('.7'),4),
                   (mp.mpc('1.2','.6'),mp.mpf(2),3)):
        sigma=s.real;a=sigma-1;c=2*mp.sqrt(w)
        assert c>max(a,0)/(M+1)
        actual=4/(mp.sqrt(mp.pi)*mp.gamma(s))*sum(
            (-1)**m*(m/mp.sqrt(w))**(s-mp.mpf('.5'))*
            mp.besselk(s-mp.mpf('.5'),2*m*mp.sqrt(w))
            for m in range(M+1,M+61))
        bound=4*w**(-sigma/2)/abs(mp.gamma(s))*mp.exp(
            (sigma-mp.mpf('.5'))**2/(4*(M+1)*mp.sqrt(w)))*(
            (M+1)**(sigma-1)*mp.exp(-2*(M+1)*mp.sqrt(w)))/(
            1-mp.exp(-2*mp.sqrt(w)+max(sigma-1,0)/(M+1)))
        assert abs(actual)<bound
        tails.append({'s':str(s),'w':str(w),'M':M,
                      'sixty_term_omitted_K_sum_modulus':mp.nstr(abs(actual),30),
                      'proved_tail_bound':mp.nstr(bound,30)})
    result={'mpmath_dps':90,'gamma_residue_checks':residue,
            'Barnes_integral_checks':rows,'Bessel_tail_checks':tails,
            'scope':'independent point quadrature; exact polynomial degeneracy checks',
            'passed':True}
    path=HERE/'root-coefficient-review-results.json'
    path.write_text(json.dumps(result,indent=2))
    print('PASS:13 shifted Gamma residues,16 Barnes integral reductions,2 Bessel tails.')
    print(path)


if __name__=='__main__':main()
