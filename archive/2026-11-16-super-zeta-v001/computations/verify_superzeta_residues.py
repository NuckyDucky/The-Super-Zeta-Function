"""Exact shifted residues and directed shifted-superzeta Mellin evaluation."""
from pathlib import Path
from fractions import Fraction
import json
import time
import sympy as sy
import mpmath as mp
from flint import arb,acb,ctx

HERE=Path(__file__).resolve().parent
ctx.prec=512;mp.mp.dps=160


def exact_residues():
    rows=[]
    z=sy.symbols('z')
    for n in range(25):
        B=sy.Rational(sy.binomial(2*n,n),4**n)
        gamma_residue=sy.simplify((-1)**n/(sy.factorial(n)*sy.sqrt(sy.pi)*sy.gamma(sy.Rational(1,2)-n)))
        assert sy.simplify(gamma_residue-B/sy.pi)==0
        assert sy.simplify((-1)**n*sy.rf(sy.Rational(1,2)-n,n)/sy.factorial(n)-B)==0
        rows.append({'n':n,'pole':str(sy.Rational(1,2)-n),'normalized_residue':str(B),
                     'balanced_words':str(sy.binomial(2*n,n)),'all_words':str(4**n)})
    return rows


def H(v,eps,analytic):
    u=v.sqrt(analytic=analytic)
    return ((1-u)/eps**2-(1+(-2*u).exp())/(2*u))/(u.cosh()**2+v/eps**2)


def Hu(u,eps):
    return ((1-u)/eps**2-(1+(-2*u).exp())/(2*u))/(u.cosh()**2+u*u/eps**2)


def integral(s,w,eps):
    ss=arb(s.numerator)/s.denominator;ww=arb(w);ee=arb(eps);u0=ww.sqrt()
    power=3-4*s;assert power.denominator==1 and power>=0
    def low(q,analytic):
        u=u0+q**4
        return 8*u*q**int(power)*(-ss*(2*u0+q**4).log(analytic=analytic)).exp()*Hu(u,ee)
    def high(u,analytic):
        return 2*u*(-ss*(u*u-ww).log(analytic=analytic)).exp()*Hu(u,ee)
    tol=arb(2)**(-300)
    out=acb.integral(low,0,1,rel_tol=tol,abs_tol=tol,eval_limit=20000)
    for a,b in ((u0+1,4),(4,12),(12,40),(40,120)):
        out+=acb.integral(high,a,b,rel_tol=tol,abs_tol=tol,eval_limit=20000)
    T=arb(120)
    def tailpow(a):
        den=2-a/T if a>0 else arb(2)
        assert den>0
        return T**a*(-2*T).exp()/den
    factor=(1-ww/T**2)**(-ss) if ss>0 else arb(1)
    bound=8*factor*((tailpow(1-2*ss)+tailpow(2-2*ss))/ee**2+tailpow(-2*ss))
    assert out.is_finite() and out.imag.contains(0)
    return arb(out.real,bound),bound


def shifted_values():
    rows=[]
    for eps in ('1','2'):
        for w in ('1','4'):
            for s in (Fraction(-1,4),Fraction(0),Fraction(1,4),Fraction(3,4)):
                I,tail=integral(s,w,eps);ss=arb(s.numerator)/s.denominator
                ww=arb(w);ee=arb(eps);Q=ww.sqrt().cosh()**2+ww/ee**2
                if s==0:
                    derivative=-2*ww.sqrt()+I
                    target=-(4*Q).log()
                    assert derivative.contains(target)
                    value=arb(0);det=(-derivative).exp()
                    assert det.contains(4*Q)
                else:
                    value=(ss-arb('1/2')).gamma()/(arb.pi().sqrt()*ss.gamma())*ww**(arb('1/2')-ss)
                    value+=(arb.pi()*ss).sin()/arb.pi()*I
                    derivative=None;det=None
                rows.append({'s':str(s),'w':w,'epsilon':eps,'directed_integral':str(I),
                             'absolute_integral_tail_after_u120':str(tail),'superzeta':str(value),
                             'zeta_derivative_at_zero':str(derivative) if derivative is not None else None,
                             'determinant_enclosure':str(det) if det is not None else None})
    return rows


def actual_trace_checks():
    d=mp.findroot(lambda x:mp.cos(x)-x,mp.mpf('.74'));roots=[];N=128
    for n in range(1,N+1):
        def f(t):
            theta=mp.acos(-t/mp.sinh(t))
            return theta+mp.cosh(t)*mp.sin(theta)-(n+mp.mpf('.5'))*mp.pi
        t=mp.findroot(f,(mp.log(2*mp.pi*n),mp.log(2*mp.pi*n)+mp.mpf('.1')))
        theta=mp.acos(-t/mp.sinh(t));u=mp.cosh(t)*mp.sin(theta)+1j*t
        roots.append(u*u)
    rows=[]
    for w in (mp.mpf('.25'),mp.mpf(1),mp.mpf(4)):
        Q=lambda x:mp.cosh(mp.sqrt(x))**2+x
        for m in range(1,5):
            value=(d*d+w)**(-m)+2*mp.re(sum((v+w)**(-m) for v in roots))
            exact=(-1)**(m-1)/mp.factorial(m-1)*mp.diff(lambda x:mp.log(Q(x)),w,m)
            eta=1-w/(mp.pi**2*(N+mp.mpf('.5'))**2)
            bound=2*eta**(-m)*mp.pi**(-2*m)/(2*m-1)*(N-mp.mpf('.5'))**(1-2*m)
            assert abs(value-exact)<bound
            rows.append({'w':mp.nstr(w,20),'m':m,'partial_128_quartet_trace':mp.nstr(value,70),
                         'closed_resolvent_trace':mp.nstr(exact,70),'analytic_full_tail_bound':mp.nstr(bound,35)})
    return rows


def main():
    start=time.perf_counter()
    out={'precision':{'arb_bits':ctx.prec,'mpmath_dps':mp.mp.dps},
         'exact_pole_residues':exact_residues(),'directed_shifted_Mellin_checks':shifted_values(),
         'actual_spectrum_positive_integer_traces':actual_trace_checks(),
         'scope':'Exact algebra and analytic tail proofs; directed Mellin/determinant enclosures; point spectral trace comparisons',
         'elapsed_seconds':time.perf_counter()-start,'passed':True}
    (HERE/'superzeta-residue-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('PASS: 25 exact residues, 16 directed shifted integrals, four determinant enclosures and 12 actual-spectrum traces.')
    print('Elapsed seconds:',out['elapsed_seconds'])


if __name__=='__main__':main()
