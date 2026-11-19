"""Directed finite prefix + analytic infinite tail for the quarter shift.

The proofs are in research/global-quarter-shift-trajectory.md. CPU only.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
import json
import time
from flint import arb, acb, ctx
import mpmath as mp
HERE=Path(__file__).resolve().parent
ctx.prec=512;mp.mp.dps=100

def ra(v):
    v=Fraction(v);return arb(v.numerator)/v.denominator

def radial(t):
    a=t/t.sinh();return (-a).acos()+t.cosh()*(1-a*a).sqrt()

def isolate(n):
    target=(2*n+1)*arb.pi()/2;lo,hi=Fraction(1,2),Fraction(2)
    assert radial(ra(lo))<target
    while not radial(ra(hi))>target:hi*=2
    for _ in range(360):
        mid=(lo+hi)/2;f=radial(ra(mid))-target
        if f>0:hi=mid
        elif f<0:lo=mid
        else:raise ArithmeticError('Increase precision')
    t=arb(ra((lo+hi)/2),ra((hi-lo)/2))
    return t,(t/t.tanh()).exp(),str(lo),str(hi)

def continuous_mp(t):
    a=t/mp.sinh(t);theta=mp.acos(-a)
    q=mp.sqrt(mp.sinh(t)**2-t*t);h=t/mp.tanh(t)
    fp=q+(h-1)**2/q
    x=(theta+mp.cosh(t)*mp.sqrt(1-a*a))/mp.pi-mp.mpf('.5')
    B=mp.gamma(x+mp.mpf('.5'))/(mp.sqrt(mp.pi)*mp.gamma(x+1))
    level=x*mp.exp(h)*B*B/2
    hprime=mp.coth(t)-t/mp.sinh(t)**2
    derivative=1-level*(mp.pi*hprime/fp+1/x
                           +2*mp.digamma(x+mp.mpf('.5'))-2*mp.digamma(x+1))
    return x,x-level,derivative

def main():
    start=time.perf_counter();rows=[];deltas=[]
    for n in range(1,128):
        t,R,lo,hi=isolate(n)
        B=arb(comb(2*n,n))/arb(4**n)
        level=n*R*B*B/2;delta=n-level
        hurwitz=-ra(Fraction(1,12))+delta/2-delta*delta/2
        actual_hurwitz=acb(-1).zeta(1-delta)
        assert (actual_hurwitz-acb(hurwitz)).contains(0)
        assert delta>0 and delta<ra(Fraction(1,4))
        assert R>2*arb.pi()*n
        if n<=28:assert hurwitz<0
        else:assert hurwitz>0
        if n==2:assert t>2
        deltas.append(delta)
        rows.append({'n':n,'t':t.str(60),'R':R.str(65),
          'Lambda':level.str(65),'delta':delta.str(65),
          'Hurwitz_minus_one':hurwitz.str(65),
          'actual_Hurwitz_argument_1_minus_delta':(1-delta).str(65),
          'Hurwitz_polynomial_residual':(actual_hurwitz-acb(hurwitz)).str(20),
          'rational_t_bracket':[lo,hi]})
    assert all(deltas[n-1]>deltas[1] for n in range(1,128) if n!=2)
    N=128;L=(2*arb.pi()*N).log();A=2*arb.pi()*N
    eta=256*(1+L)**2/A**2
    chi_up=(2*L*L-2*L-1)/A**2+eta**2/(8*(1-eta))
    lower=ra(Fraction(1,4))-N*chi_up-ra(Fraction(1,96*N*N))-ra(Fraction(1,32*N))
    critical=(1-1/arb(3).sqrt())/2
    assert eta<1
    assert L>(3+arb(7).sqrt())/2
    assert lower>critical and lower>deltas[1]
    assert N*chi_up+ra(Fraction(1,96*N*N))<ra(Fraction(1,4))
    # Exact constants used in the t>=2 elementary R>A inequality.
    assert 2/arb(2).sinh()<ra(Fraction(3,5))
    assert (-arb(4)).exp()<ra(Fraction(1,25))
    assert 2*arb(2)**2-ra(Fraction(25,8))*2-1>0
    tc=mp.findroot(lambda t:continuous_mp(t)[2],(mp.mpf('2.3'),mp.mpf('2.5')))
    xc,dc,der=continuous_mp(tc)
    # This local stationary location is a point record; the discrete global
    # minimum and the full sign theorem above are directed/analytic.
    out={'status':'all 127 directed prefix levels and analytic infinite-tail gates passed',
      'precision':{'arb_bits':ctx.prec,'rational_bisection_steps':360,
                   'stationary_point_mpmath_dps':mp.mp.dps},
      'finite_prefix':rows,'unique_global_discrete_minimum_index':2,
      'unique_global_discrete_sign_change':'negative for n<=28; positive for every n>=29',
      'tail_start':N,'eta_at_tail_start':eta.str(60),
      'uniform_delta_lower_for_all_n_ge_128':lower.str(80),
      'global_delta_upper':'1/4, strict',
      'Hurwitz_critical_delta':critical.str(80),
      'continuous_stationary_point_record':{'scope':'100-digit point calculation',
        't':mp.nstr(tc,90),'x':mp.nstr(xc,90),'delta':mp.nstr(dc,90),
        'delta_prime':mp.nstr(der,20)},
      'elapsed_seconds':time.perf_counter()-start}
    (HERE/'global-quarter-shift-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(out['status']);print('seconds',out['elapsed_seconds'])
    print('delta2',deltas[1].str(60));print('tail lower',lower.str(60))

if __name__=='__main__':main()
