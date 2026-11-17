"""Exact and directed checks of the central-binomial quartet normalization.

CPU only. The companion note proves the Barnes product, strict Stirling
remainder, radial-tail estimate and meromorphic deformed-zeta theorem.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import math
import time
import mpmath as mp
import sympy as sp
from flint import arb, acb, acb_series, ctx

HERE=Path(__file__).resolve().parent
ctx.prec=384;ctx.cap=12;mp.mp.dps=100
L,W,S=sp.symbols('ell w s')
INPUT=json.loads((HERE.parent/'sources'/'radial-coefficient-input.json').read_text())
CHI=[sp.sympify(v,locals={'ell':L}) for v in INPUT['log_radius_chi']]
J=4;M=4;NMAX=1024;STEPS=220

def ra(value):
    q=Fraction(value);return arb(q.numerator)/q.denominator

def bernoulli_coefficient(m):
    return sp.Rational(-4)*(1-sp.Rational(1,2)**(2*m))*sp.bernoulli(2*m)/(2*m*(2*m-1))

def exact_formal():
    d={2*m-1:bernoulli_coefficient(m) for m in range(1,6)}
    assert [d[k] for k in [1,3,5,7,9]]==[
        sp.Rational(-1,4),sp.Rational(1,96),sp.Rational(-1,320),
        sp.Rational(17,7168),sp.Rational(-31,9216)]
    e=[]
    for r in range(2,10):
        rhs=d.get(r,0)+sp.Rational(1,4*r)
        previous=sum(sp.binomial(r-1,k-1)*e[k-1] for k in range(1,r-1))
        e.append(sp.expand(-(rhs+previous)/(r-1)))
    u={m:sp.Integer(0) for m in range(1,9)}
    for m in range(1,9):
        if m%2:u[m]=d[m]
        else:u[m]=CHI[m//2-1]/(2*sp.pi)**m
    E=[sp.Integer(1)]
    for m in range(1,9):
        E.append(sp.expand(W*sum(k*u[k]*E[m-k] for k in range(1,m+1))/m))
        j=m//2
        expected=(sp.binomial(W/2,j)/sp.pi**(2*j) if m%2==0 else
                  -W*sp.binomial(W/2,j)/(4*sp.pi**(2*j)))
        assert sp.simplify(E[m].coeff(L,2*j)-expected)==0
        if m>=2:
            top=sp.expand(E[m].subs(W,m-1)).coeff(L,2*j)
            assert top!=0
    assert E[1]==-W/4
    return d,e,E

def radial(t):
    c=-t/t.sinh();return c.acos()+t.cosh()*(1-c*c).sqrt()

def isolate(n):
    target=(2*n+1)*arb.pi()/2
    lo,hi=Fraction(1,2),Fraction(2)
    while not radial(ra(hi))>target:hi*=2
    assert radial(ra(lo))<target
    for _ in range(STEPS):
        mid=(lo+hi)/2;value=radial(ra(mid))-target
        if value>0:hi=mid
        elif value<0:lo=mid
        else:raise ArithmeticError('increase directed precision')
    assert radial(ra(lo))<target and radial(ra(hi))>target
    t=arb(ra((lo+hi)/2),ra((hi-lo)/2))
    return (t/t.tanh()).exp(),lo,hi

def moment(poly,q,N):
    pp=sp.Poly(poly,L);degree=pp.degree()
    z=acb_series([q,1],prec=degree+1)
    H=(-z*(2*arb.pi()).log()).exp()*z.zeta(N+1)
    out=arb(0)
    for (k,),coefficient in pp.terms():
        out+=ra(str(coefficient))*(-1)**k*math.factorial(k)*H[k].real
    return out

def radial_tail(N):
    approximate=sum((moment(poly,2*j,N) for j,poly in enumerate(CHI,1)),arb(0))
    A=2*arb.pi()*N;ell=1+A.log();eta=256*ell**2/A**2
    assert eta<1
    k=2*J+2;p=k
    integral=(2*arb.pi())**(-p)*arb(N)**(1-p)*sum(
        math.comb(k,j)*ell**(k-j)*math.factorial(j)/arb(p-1)**(j+1)
        for j in range(k+1))
    error=256**(J+1)*integral/(8*(1-eta))
    return approximate,error

def stirling_tail(N,d):
    approximation=-(arb(N+1).digamma()-arb(N).log())/4
    for m in range(2,M+1):
        approximation-=ra(str(d[2*m-1]))*acb(2*m-1).zeta(N+1).real
    error=abs(ra(str(d[2*M+1])))*acb(2*M+1).zeta(N+1).real
    return approximation,error

def logG(x):return acb(x).log_barnes_g().real

def dottie():
    lo,hi=Fraction(73,100),Fraction(74,100)
    assert ra(lo).cos()-ra(lo)>0 and ra(hi).cos()-ra(hi)<0
    for _ in range(260):
        mid=(lo+hi)/2;v=ra(mid).cos()-ra(mid)
        if v>0:lo=mid
        elif v<0:hi=mid
        else:raise ArithmeticError('increase precision')
    return arb(ra((lo+hi)/2),ra((hi-lo)/2))

def main():
    start=time.perf_counter();d,e,E=exact_formal()
    db=dottie();sine=db.sin();g=acb(ra(Fraction(3,2))).barnes_g().real
    logK=sine/2-2*g.log();K=logK.exp()
    dm=mp.findroot(lambda x:mp.cos(x)-x,mp.mpf('.74'))
    independent_K=mp.exp(mp.sin(dm)/2)/mp.barnesg(mp.mpf('1.5'))**2
    assert K.contains(arb(mp.nstr(independent_K,95)))
    sumC=arb(0);sumD=arb(0);records=[];levels=[];digest=hashlib.sha256()
    for n in range(1,NMAX+1):
        R,lo,hi=isolate(n);digest.update(f'{n}:{lo}:{hi}\n'.encode())
        B=arb(math.comb(2*n,n))/arb(4**n)
        D=arb.pi()*n*B**2;C=R*B**2/2
        assert (C-(R/(2*arb.pi()*n))*D).contains(0)
        sumC+=C.log();sumD+=D.log()
        if n in [1,2,4,8,16,64,256,512,1024]:
            levels.append({'n':n,'B_n':B.str(45),'C_n':C.str(45),
                           'n_C_n':(n*C).str(45)})
        if n in [16,64,256,512,1024]:
            barnes_log=arb(n+1).lgamma()+2*logG(arb(n)+ra(Fraction(3,2)))-2*logG(n+2)-2*g.log()
            assert (sumD-barnes_log).contains(0)
            exact_D_correction=arb(n).log()/4+barnes_log+2*g.log()
            approx_D,error_D=stirling_tail(n,d)
            assert abs(exact_D_correction-approx_D)<error_D
            bare_log=arb(n).log()/4+sumC
            record={'N':n,'direct_normalized_product':bare_log.exp().str(60),
                    'exact_Barnes_log_correction':exact_D_correction.str(60),
                    'Stirling_tail_approximation':approx_D.str(60),
                    'Stirling_tail_error_bound':error_D.str(45),
                    'Barnes_finite_product_identity_residual':(sumD-barnes_log).str(20)}
            if n>=512:
                radial_approx,radial_error=radial_tail(n)
                corrected=arb(bare_log-approx_D+radial_approx,error_D+radial_error)
                assert corrected.contains(logK)
                record.update({'radial_tail_approximation':radial_approx.str(60),
                      'radial_tail_error_bound':radial_error.str(45),
                      'corrected_log_constant':corrected.str(60),
                      'corrected_constant':corrected.exp().str(60),
                      'difference_from_exact_log_constant':(corrected-logK).str(35)})
            records.append(record)
    out={'status':'all exact formal, directed Barnes-product and controlled-cutoff checks passed',
         'precision':{'arb_bits':ctx.prec,'independent_mpmath_dps':mp.mp.dps,
                      'radial_bisections':STEPS,'maximum_level':NMAX,
                      'radial_order':J,'Stirling_order':M},
         'root_bracket_stream_sha256':digest.hexdigest(),
         'G_three_halves':g.str(85),'exact_limit_constant':K.str(85),
         'independent_100dps_limit_constant':mp.nstr(independent_K,85),
         'exact_limit_formula':'exp(sin(d)/2)/G(3/2)^2, d=cos(d)',
         'effective_spectrum_zeta_at_zero':'-1/4',
         'effective_spectrum_zeta_determinant':((2*arb.pi()).sqrt()*K).str(85),
         'formal':{'log_D_coefficients':{str(k):str(v) for k,v in d.items()},
                   'Barnes_log_cutoff_coefficients':[str(v) for v in e],
                   'deformed_zeta_coefficients_E0_to_E4':[str(v) for v in E[:5]],
                   'all_highest_log_coefficients_verified_through_m':8},
         'selected_levels':levels,'finite_cutoff_checks':records,
         'elapsed_seconds':time.perf_counter()-start}
    (HERE/'binomial-normalization-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(out['status']);print('K:',out['exact_limit_constant'])
    print('det:',out['effective_spectrum_zeta_determinant'])
    print('seconds:',out['elapsed_seconds'])

if __name__=='__main__':main()
