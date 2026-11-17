"""Laplace/Barnes coefficient hierarchy, directed coupling tails and references.

Headless CPU only. Exact integer/Fraction identities; 400-step Laplace
isolation at512 bits; coefficient balls at832 bits; cached eta points at
250 decimal digits; independent positive quadrature at90 decimal digits.
"""
from pathlib import Path
from fractions import Fraction
from math import factorial,comb
from functools import cache
import hashlib
import json
import time
import mpmath as mp
from flint import arb,ctx

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
mp.mp.dps=250
ETA={}


def ar(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator


def mpr(q):
    q=Fraction(q)
    return mp.mpf(q.numerator)/q.denominator


def laplace_isolation():
    ctx.prec=512
    lo,hi=Fraction(1),Fraction(3,2)
    for _ in range(400):
        mid=(lo+hi)/2
        value=ar(mid)*ar(mid).tanh()-1
        if value>0:hi=mid
        elif value<0:lo=mid
        else:raise ArithmeticError('unresolved directed Laplace sign')
    nu=arb(ar((lo+hi)/2),ar((hi-lo)/2))
    RL=nu/nu.cosh()
    assert RL>0 and RL<1
    g2=-2/nu**2-2/nu.cosh()**2
    assert g2.contains(-2)
    return nu,RL,{'arb_bits':512,'bisection_steps':400,
                  'exact_nu_bracket':[str(lo),str(hi)],
                  'nu':str(nu),'R_L':str(RL),'R_L_squared':str(RL**2),
                  'g_second_derivative':str(g2)}


@cache
def P(m):
    poly={1:1}
    for j in range(1,m):
        nxt={}
        for degree,value in poly.items():
            nxt[degree+2]=nxt.get(degree+2,0)+value
            nxt[degree]=nxt.get(degree,0)-j*j*value
        poly=nxt
    return poly


def eta(q):
    q=Fraction(q)
    if q not in ETA:
        qq=ar(q)
        directed=arb(2).log() if q==1 else (1-((1-qq)*arb(2).log()).exp())*qq.zeta()
        point=mp.log(2) if q==1 else mp.altzeta(mpr(q))
        ETA[q]=(point,directed)
    return ETA[q]


@cache
def I(m,s):
    s=Fraction(s)
    p=2*m-2*s
    point_sum=mp.fsum(c*eta(p-j)[0] for j,c in P(m).items())
    directed_sum=sum(c*eta(p-j)[1] for j,c in P(m).items())
    sign=(-1)**(m+1)
    factor=mp.power(2,2*mpr(s)+1)*mp.gamma(mpr(p))*sign/factorial(2*m-1)
    dfactor=((2*ar(s)+1)*arb(2).log()).exp()*ar(p).gamma()*sign/factorial(2*m-1)
    return factor*point_sum,dfactor*directed_sum


def exact_polynomial_checks():
    rows=[];checked=0
    for m in range(1,37):
        for n in range(1,m+7):
            value=sum(c*n**j for j,c in P(m).items())
            target=0 if n<m else factorial(2*m-1)*comb(n+m-1,2*m-1)
            assert value==target
            checked+=1
        # The finite eta reduction's alternating signs are exact integers.
        for n in range(m,m+7):
            assert (-1)**(n-m)==(-1)**(m+1)*(-1)**(n-1)
        if m<=8:rows.append({'m':m,'P_m_integer_coefficients':P(m)})
    return {'maximum_m':36,'exact_degeneracy_evaluations':checked,
            'alternating_sign_evaluations':36*7,'first_eight_polynomials':rows}


def integral_checks():
    rows=[]
    for m in (1,2,3,6):
        for s in (Fraction(-1,4),Fraction(1,4),Fraction(3,4)):
            point,directed=I(m,s)
            with mp.workdps(90):
                ss=mpr(s);power=8*m-8*s-1
                assert power.denominator==1 and power>=0
                low=lambda q:8*q**int(power)/mp.cosh(q**4)**(2*m)
                high=lambda x:2*x**(2*m-2*ss-1)/mp.cosh(x)**(2*m)
                value=mp.quad(low,[0,1])+mp.quad(high,[1,4,12,40,120])
                aa=2*m-2*ss-1;T=mp.mpf(120)
                den=2*m-max(aa,0)/T
                tail=mp.power(2,2*m+1)*T**aa*mp.exp(-2*m*T)/den
                difference=abs(value-point)
                assert difference<mp.mpf('1e-75')+tail
                # Point-versus-ball comparison has an explicit point tolerance.
                assert abs(directed-arb(mp.nstr(value,85)))<arb('1e-75')
                rows.append({'m':m,'s':str(s),
                             'coefficient_250dps':mp.nstr(point,120),
                             'coefficient_directed_ball':str(directed),
                             'independent_90dps_integral':mp.nstr(value,85),
                             'point_difference':mp.nstr(difference,30),
                             'quadrature_cutoff_x':'120',
                             'analytic_integral_tail_bound':mp.nstr(tail,30)})
    return rows


def load_reference():
    folder=ROOT/'sources'/'foundation'
    provenance=json.loads((folder/'cosine-reference-provenance.json').read_text())
    path=folder/provenance['file'];data=path.read_bytes()
    assert hashlib.sha256(data).hexdigest()==provenance['sha256']
    old=json.loads(data)
    lookup={(Fraction(row['s']),Fraction(row['epsilon'])):row
            for row in old['directed_Mellin_checks']}
    return lookup,provenance


def coupling_checks(RL):
    reference,provenance=load_reference()
    rows=[]
    for s in (Fraction(-1,4),Fraction(1,4),Fraction(3,4)):
        ss=ar(s);pref=ss*(arb.pi()*ss).sin()/arb.pi()
        ppref=mpr(s)*mp.sin(mp.pi*mpr(s))/mp.pi
        I1=I(1,s)[1]
        for eps in (Fraction(1),Fraction(2)):
            ee=ar(eps);q=RL**2/ee**2
            assert q>0 and q<1
            old=reference[(s,eps)];target=arb(old['entire_correction'])
            for M in (12,36):
                partial=pref*sum((-1)**(m-1)*I(m,s)[1]/(m*ee**(2*m))
                                 for m in range(1,M+1))
                point=ppref*mp.fsum((-1)**(m-1)*I(m,s)[0]/(m*mpr(eps)**(2*m))
                                   for m in range(1,M+1))
                tail=abs(pref)*I1/ee**2*q**M/((M+1)*(1-q))
                enclosing=arb(partial,tail)
                assert enclosing.contains(target)
                assert abs(partial-target)<tail
                rows.append({'s':str(s),'epsilon':str(eps),'M':M,
                             'point_partial_250dps':mp.nstr(point,150),
                             'directed_finite_partial_sum':str(partial),
                             'directed_analytic_tail_bound':str(tail),
                             'directed_sum_plus_tail_enclosure':str(enclosing),
                             'frozen_directed_Mellin_reference':str(target),
                             'entire_reference_ball_contained':True,
                             'tail_ratio_q':str(q)})
    return rows,provenance


def asymptotic_checks():
    rows=[]
    with mp.workdps(90):
        nu=mp.findroot(lambda x:x*mp.tanh(x)-1,mp.mpf('1.2'))
        r0=(nu/mp.cosh(nu))**2
        for s in (mp.mpf(0),mp.mpf('.25')):
            previous=mp.inf
            for m in (16,32,64):
                def fun(x):
                    if not x:return mp.mpf(0)
                    return 2*x**(-2*s-1)*(x*x/mp.cosh(x)**2/r0)**m
                value=mp.quad(fun,[0,mp.mpf('.5'),1,nu,mp.mpf('1.5'),2,4,12,40])
                leading=2*mp.sqrt(mp.pi)*nu**(-2*s-1)/mp.sqrt(m)
                ratio=value/leading
                error=abs(ratio-1)
                assert error<previous;previous=error
                T=mp.mpf(40);aa=2*m-2*s-1
                tail=mp.power(2,2*m+1)*T**aa*mp.exp(-2*m*T)/(2*m-aa/T)/r0**m
                rows.append({'m':m,'s':str(s),'positive_quadrature_cutoff_x':'40',
                             'I_m_over_R_L_power':mp.nstr(value,80),
                             'ratio_to_proved_Laplace_leading_term':mp.nstr(ratio,65),
                             'absolute_deviation_from_one':mp.nstr(error,30),
                             'analytic_normalized_integral_tail_bound':mp.nstr(tail,30),
                             'scope':'90-digit positive point quadrature; asymptotic theorem is analytic'})
    return rows


def main():
    start=time.perf_counter()
    nu,RL,isolation=laplace_isolation()
    ctx.prec=832
    exact=exact_polynomial_checks()
    integrals=integral_checks()
    coupling,reference=coupling_checks(RL)
    asymptotics=asymptotic_checks()
    eta_records=[{'argument':str(q),'point_250dps':mp.nstr(point,120),
                  'directed_832bit_ball':str(ball)}
                 for q,(point,ball) in sorted(ETA.items())]
    result={'precision':{'Laplace_isolation_arb_bits':512,
                         'coefficient_arb_bits':832,'eta_point_decimal_digits':250,
                         'independent_quadrature_decimal_digits':90,
                         'frozen_reference_arb_bits':512},
            'Laplace_isolation':isolation,'exact_polynomial_checks':exact,
            'coefficient_integral_checks':integrals,
            'coupling_partial_sum_checks':coupling,
            'frozen_reference_provenance':reference,
            'positive_Laplace_asymptotic_checks':asymptotics,
            'cached_eta_values':eta_records,
            'status':'all directed Laplace, exact degeneracy/sign, coefficient integral, coupling-tail and point asymptotic checks passed',
            'passed':True,'elapsed_seconds':time.perf_counter()-start}
    path=HERE/'laplace-barnes-results.json'
    path.write_text(json.dumps(result,indent=2),encoding='utf-8')
    print('PASS:',result['status'])
    print('Seconds:',round(result['elapsed_seconds'],3))
    print(path)


if __name__=='__main__':main()
