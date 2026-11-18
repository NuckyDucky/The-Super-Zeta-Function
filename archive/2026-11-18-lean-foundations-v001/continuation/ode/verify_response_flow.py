"""Exact ODE/jet identities and certified Dottie continuation/error bounds.

Python 3.12; SymPy 1.14, mpmath 1.3, python-flint 0.9.  Arb comparisons
establish the finite inequalities used in the analytical continuation theorem.
"""
from pathlib import Path
from fractions import Fraction
import json
import sympy as S
import mpmath as mp
from flint import arb,acb,ctx

HERE=Path(__file__).resolve().parent
ctx.prec=1024

def arbrat(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator

def certified_dottie(iterations=500):
    low,high=Fraction(73,100),Fraction(74,100)
    assert arbrat(low).cos()-arbrat(low)>0
    assert arbrat(high).cos()-arbrat(high)<0
    for _ in range(iterations):
        mid=(low+high)/2;value=arbrat(mid).cos()-arbrat(mid)
        if value>0:low=mid
        elif value<0:high=mid
        else:raise ArithmeticError('increase interval precision')
    d=arb(arbrat((low+high)/2),arbrat((high-low)/2))
    return d,low,high

def exact_checks():
    U,V,a,m,c=S.symbols('U V a mu c')
    Ut=U*(1+V)/(1-U*V);Vt=V*(1+U)/(1-U*V)
    assert S.factor((Ut+Vt)/2-((U+V)/2+U*V)/(1-U*V))==0
    assert S.factor(Ut*V+U*Vt-2*U*V*(1+(U+V)/2)/(1-U*V))==0
    fa=(a+m)/(1-m);fm=2*m*(1+a)/(1-m)
    second=S.diff(fm,a)*fa+S.diff(fm,m)*fm
    assert S.factor(m*(1-m)*second-fm**2-m*fm+2*m*m)==0
    assert S.expand(2*m*(1+a)-2*a*(a+m)-2*(m-a*a))==0
    assert S.expand((1+V)-V*(1+U)-(1-U*V))==0
    aa=[c];mm=[S.Integer(1)]
    for n in range(12):
        aa.append(S.expand((aa[n]+mm[n])/S.Integer(n+1)))
        mm.append(S.expand(2*(mm[n]+sum(aa[j]*mm[n-j] for j in range(n+1)))/S.Integer(n+1)))
    tt=[S.Integer(0),S.Integer(0)]+[-mm[n-1]/S.Integer(n) for n in range(2,13)]
    H=[S.Integer(0)]+[S.cancel(mm[n+1]/((n+2)*(1+c))) for n in range(1,10)]
    for term in aa+mm+H:S.Poly(term,c)
    # Lagrange inversion: [w^n] zeta(w) = [zeta^(n-1)](1+H)^(-n/2)/n.
    def multiply(x,y,N):
        return [S.expand(sum(x[j]*y[k-j] for j in range(k+1))) for k in range(N)]
    inverse=[]
    for n in range(1,9):
        N=n;hh=H[:N];power=[S.Integer(1)]+[S.Integer(0)]*(N-1)
        value=S.Integer(0)
        for k in range(n):
            value+=S.binomial(-S.Rational(n,2),k)*power[n-1]
            power=multiply(power,hh,N)
        value=S.factor(value/n);S.Poly(value,c);inverse.append(value)
    assert inverse[0]==1
    assert S.factor(inverse[1]+(2*c+3)/6)==0
    return {'status':'exact symbolic identities passed',
      'scalar_multiplier_equation':'mu*(1-mu)*mu_tt-mu_t^2-mu*mu_t+2*mu^2=0',
      'a_coefficients_0_through_12':[str(S.factor(x)) for x in aa],
      'mu_coefficients_0_through_12':[str(S.factor(x)) for x in mm],
      'log_parameter_coefficients_0_through_12':[str(S.factor(x)) for x in tt],
      'inverse_fold_coefficients_1_through_8':[str(x) for x in inverse],
      'coefficient_field':'all displayed coefficients are polynomials in c=sin(d) over Q'}

def flow_arb(d,c,z):
    u=d*z.exp();a=u*u.tan();mu=(u/u.cos())**2
    tau=z+(d.cos()/u.cos()).log()-a+c
    return a,mu,tau

def psi_arb(d,c,z):
    a,mu,tau=flow_arb(d,c,z)
    return z*(-tau/((1+c)*z*z)).sqrt()

def certified_checks():
    d,low,high=certified_dottie();c=d.sin();C=1+c
    q=arb(1)/4;r=arb(1)/2;testq=arb(1)/10
    aq,mq,tq=flow_arb(d,c,q)
    h=-tq/(C*q*q)-1
    beta=q*(1-h).sqrt()
    assert h>0 and h<arb(5)/9
    assert -tq<arb(1)/5
    assert beta>arb(1)/6
    rho=(arb.pi()/(2*d)).log()
    assert rho>arb(3)/4
    N=80;aa=[c];mm=[arb(1)]
    for n in range(N):
        aa.append((aa[n]+mm[n])/(n+1))
        mm.append(2*(mm[n]+sum((aa[j]*mm[n-j] for j in range(n+1)),arb(0)))/(n+1))
    tt=[arb(0),arb(0)]+[-mm[n-1]/n for n in range(2,N+1)]
    ar,mr,tr=flow_arb(d,c,r)
    bounds=[ar*(testq/r)**(N+1),mr*(testq/r)**(N+1),
            testq*mr/(N+1)*(testq/r)**N]
    def eval_series(coeff,z):
        out=acb(0)
        for coeffvalue in reversed(coeff):out=out*z+coeffvalue
        return out
    points=[acb(testq),acb(-testq),acb(arb(3)/50,arb(4)/50),
            acb(-arb(4)/50,arb(3)/50)]
    comparisons=[]
    for z in points:
        direct=flow_arb(d,c,z)
        approximants=[eval_series(p,z) for p in [aa,mm,tt]]
        errors=[abs(x-y) for x,y in zip(direct,approximants)]
        for error,bound in zip(errors,bounds):assert error<bound
        comparisons.append({'zeta':z.str(60),
          'actual_interval_errors':[x.str(30) for x in errors],
          'proved_tail_bounds':[x.str(30) for x in bounds]})
    return d,c,{
      'status':'certified inequalities and Taylor-tail comparisons passed',
      'interval_precision_bits':ctx.prec,'dottie_bisection_steps':500,
      'dottie_exact_bracket':[str(low),str(high)],
      'dottie_interval':d.str(90),'c_interval':c.str(90),
      'exact_series_radius_log_phase':rho.str(90),
      'rouche_q':'1/4','H_at_q':h.str(90),'H_upper_rational':'5/9',
      'inverse_w_radius_lower':'1/6','actual_rouche_w_radius':beta.str(90),
      'proved_log_parameter_radius':'(1+sin(d))/36',
      'proved_log_parameter_radius_interval':(C/36).str(90),
      'inverse_defect_lipschitz_core':'24/7 for |w|,|psi(zeta_approx)| <= 1/8',
      'tail_degree':N,'tail_r':'1/2','tail_test_q':'1/10',
      'tail_comparisons':comparisons}

def inverse_samples(d,c):
    with mp.workdps(220):
        dm=mp.findroot(lambda z:mp.cos(z)-z,mp.mpf('.74'))
        cm=mp.sin(dm);Cm=1+cm
        def tau(z):
            u=dm*mp.exp(z);a=u*mp.tan(u)
            return z+mp.log(mp.cos(dm)/mp.cos(u))-a+cm
        def psi(z):return z*mp.sqrt(-tau(z)/(Cm*z*z))
        targets=[(-1,0,100),(1,0,100),(1,1,100),(0,-1,50)]
        records=[]
        aq,mq,tq=flow_arb(d,c,arb(1)/4)
        Mmu=2*mq*(1+aq)
        Mlogphase=aq+mq+d*(arb(1)/4).exp()
        for real,imag,den in targets:
            tm=mp.mpc(real,imag)/den
            ta=acb(arb(real)/den,arb(imag)/den)
            wbase=mp.sqrt(-tm/Cm)
            for sign in [1,-1]:
                wm=sign*wbase
                root=mp.findroot(lambda z:psi(z)-wm,wm)
                zr=mp.nstr(mp.re(root),70);zi=mp.nstr(mp.im(root),70)
                z=acb(arb(zr),arb(zi));w=sign*(-ta/(1+c)).sqrt()
                pz=psi_arb(d,c,z)
                assert abs(z)<arb(1)/4
                assert abs(w)<arb(1)/8 and abs(pz)<arb(1)/8
                defect=abs(pz-w);zeta_error=arb(24)/7*defect
                assert zeta_error<arb('1e-65')
                av,muv,tv=flow_arb(d,c,z)
                um=dm*mp.exp(root);am=um*mp.tan(um)
                Lm=1j*(um/mp.cos(um))*mp.exp(-am)
                Pm=mp.exp(am+1j*um);Qm=mp.exp(am-1j*um)
                residual=max(abs(mp.exp(Lm*Qm)-Pm),abs(mp.exp(-Lm*Pm)-Qm),
                             abs(tau(root)-tm))
                assert residual<mp.mpf('1e-195')
                records.append({'tau':ta.str(40),'sheet_sign':sign,
                  'zeta_approx_exact_decimal':{'real':zr,'imaginary':zi},
                  'psi_defect_interval':defect.str(35),
                  'certified_zeta_error_bound':zeta_error.str(35),
                  'mu_at_approx_interval':muv.str(85),
                  'certified_mu_absolute_error_bound':(Mmu*zeta_error).str(35),
                  'certified_phase_relative_error_bound':((Mlogphase*zeta_error).exp()-1).str(35),
                  'independent_point_fixed_pair_residual':mp.nstr(residual,10)})
        return {'status':'all inverse samples certified by the analytical defect bound',
                'independent_point_precision_decimal_digits':220,
                'samples':records}

def main():
    symbolic=exact_checks()
    d,c,certified=certified_checks()
    inverse=inverse_samples(d,c)
    result={'status':'all ODE, continuation and certified-error checks passed',
            'symbolic':symbolic,'certified_continuation':certified,'inverse_samples':inverse}
    (HERE/'response-flow-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'status':result['status'],
      'certified_log_parameter_radius':certified['proved_log_parameter_radius_interval'],
      'H_at_quarter':certified['H_at_q'],'tail_cases':len(certified['tail_comparisons']),
      'certified_inverse_samples':len(inverse['samples'])},indent=2))

if __name__=='__main__':main()
