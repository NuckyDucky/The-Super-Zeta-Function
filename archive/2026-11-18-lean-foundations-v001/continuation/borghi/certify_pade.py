"""Certified Padé/Gauss--Radau bounds transferred to Nick's fixed pairs.

Borghi's measure is used in its phase variable.  After the quarter-phase
specialization, x is an auxiliary positive resolvent variable and the measure
is pushed forward by t -> t^2.  All finite decisions use Arb intervals.
"""
from pathlib import Path
from fractions import Fraction
import argparse,json,time
from flint import arb,arb_mat,acb,fmpq,ctx

HERE=Path(__file__).resolve().parent

def enc(q): return str(q.numerator)+'/'+str(q.denominator)
def point(q):return arb(fmpq(q.numerator,q.denominator))
def exact_endpoint(a,which):return Fraction(str(getattr(a,which)().fmpq()))
def ball(l,h):return arb(point((l+h)/2),point((h-l)/2))
def display(a,digits=70):return a.str(digits)

def horner(coeffs,x):
    value=arb(0)
    for c in reversed(coeffs):value=value*x+c
    return value

def pade(c,L,M,x):
    rows=[[c[k-j] for j in range(1,M+1)] for k in range(L+1,L+M+1)]
    rhs=[[-c[k]] for k in range(L+1,L+M+1)]
    sol=arb_mat(rows).solve(arb_mat(rhs))
    q=[arb(1)]+[sol[j,0] for j in range(M)]
    p=[sum((q[j]*c[k-j] for j in range(min(k,M)+1)),arb(0)) for k in range(L+1)]
    denominator=horner(q,x)
    assert denominator>0
    # Verify every defining Padé coefficient with interval residuals.
    for k in range(L+1,L+M+1):
        assert sum((q[j]*c[k-j] for j in range(M+1)),arb(0)).contains(0)
    return horner(p,x)/denominator,p,q

def root_bracket(eps,depth=600):
    lo,hi=Fraction(0),Fraction(1)
    for _ in range(depth):
        mid=(lo+hi)/2; x=point(mid);value=x-eps*x.cos()
        if value>0:hi=mid
        elif value<0:lo=mid
        else:raise ArithmeticError('Increase interval precision for bisection')
    return lo,hi

def case(eps_text,orders):
    eps=arb(eps_text)
    chi=(1-eps*eps).sqrt();lam=chi-chi.atanh();r=lam.exp();x=r*r
    maxj=2*max(orders)
    # M_j = Borghi moment m_(2j), with Bessel order 2j+1.
    moments=[2*((2*j+1)*eps).bessel_j(2*j+1)/((2*j+1)*r**(2*j+1))
             for j in range(maxj+1)]
    assert all(m>0 for m in moments)
    c=[((-1)**j)*v for j,v in enumerate(moments)]
    rl,rh=root_bracket(eps);root=ball(rl,rh)
    rows=[]
    for n in orders:
        lower,pL,qL=pade(c,n-1,n,x)
        upper,pU,qU=pade(c,n,n,x)
        lower*=r;upper*=r
        lo=exact_endpoint(lower,'lower');hi=exact_endpoint(upper,'upper')
        assert lo<rl<rh<hi
        assert 0<lo<hi<1
        ub=ball(lo,hi);a=eps*ub.sin();yb=eps*(-a).exp()
        P=acb(a,ub).exp();Q=P.conjugate();ell=acb(0,yb)
        residualP=P-(ell*Q).exp();residualQ=Q-(-ell*P).exp()
        assert residualP.contains(0) and residualQ.contains(0)
        delta=point(hi-lo)
        hh=(1+x).sqrt();qq=(hh-1)/(hh+1)
        geometric_width=8*eps.bessel_j(1)*qq**(2*n)
        uniform_width=4*(3-2*arb(2).sqrt())**(2*n)
        assert delta<geometric_width and geometric_width<uniform_width
        Ldiam_bound=eps**2*delta
        Pdiam_bound=(eps*point(hi).sin()).exp()*(1+eps**2).sqrt()*delta
        direct_a=eps*root.sin();direct_y=eps*(-direct_a).exp()
        assert yb.contains(direct_y)
        rows.append({'n':n,'lower_pade_type':[n-1,n],'upper_pade_type':[n,n],
          'u_lower_exact':enc(lo),'u_upper_exact':enc(hi),
          'u_interval':display(ub),'u_width':display(delta,25),
          'geometric_width_bound':display(geometric_width,25),
          'epsilon_uniform_width_bound':display(uniform_width,25),
          'L_imaginary_interval':display(yb),'P_interval':str(P),'Q_interval':str(Q),
          'L_diameter_analytical_bound':display(Ldiam_bound,25),
          'P_diameter_analytical_bound':display(Pdiam_bound,25),
          'lower_pade_denominator_coefficients':[display(v,35) for v in qL],
          'upper_pade_denominator_coefficients':[display(v,35) for v in qU],
          'all_checks':'Padé coefficient residuals, certified root bracket containment, propagated fixed equations passed'})
    return {'epsilon':eps_text,'lambda':display(lam),'r':display(r),
      'measure_mass_M0':display(moments[0]),'root_independent_interval':display(root),
      'root_bisection_depth':600,'rows':rows}

def main(bits):
    started=time.time();ctx.prec=bits
    orders=[1,2,4,8,16,24,32]
    cases=[case(e,orders) for e in ['0.5','0.9','1']]
    out={'status':'all certified Padé brackets and propagated fixed-pair checks passed',
      'interval_precision_bits':bits,'method':'Gauss [n-1/n] lower and Radau-zero [n/n] upper for the pushed-forward Borghi measure',
      'auxiliary_variable':'x=r(epsilon)^2; measure depends on epsilon; phase M=pi/2',
      'endpoint_epsilon_1':'positive Hausdorff measure obtained by weak limit, proved in report',
      'cases':cases,'elapsed_seconds':time.time()-started}
    (HERE/'pade-enclosures.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'interval_precision_bits':bits,
      'cases':[{ 'epsilon':r['epsilon'],'widths':[{ 'n':v['n'],'width':v['u_width']} for v in r['rows']]} for r in cases],
      'elapsed_seconds':out['elapsed_seconds']},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--bits',type=int,default=1024)
    main(parser.parse_args().bits)
