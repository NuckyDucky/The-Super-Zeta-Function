"""Quantitative Rouche certificates and complex loop/germ transport checks.

Exact rational inequalities certify covering/critical-point isolation. Arb certifies
the elementary transcendental majorants and real root brackets. Numerical loop
following is checked independently at 110 and 190 decimal digits.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json
import mpmath as mp
import sympy as S
from flint import arb,ctx

HERE=Path(__file__).resolve().parent
ctx.prec=512
A=lambda n,d=1:arb(n)/d

# Coarse exact brackets suffice for every analytical disk decision.
assert (A(73908,100000).cos()-A(73908,100000))>0
assert (A(73909,100000).cos()-A(73909,100000))<0
assert A(73908,100000).sin()>A(673,1000)
assert A(73909,100000).sin()<A(674,1000)
assert (-A(674,1000)).exp()>A(509,1000)
assert (-A(673,1000)).exp()<A(511,1000)
assert A(1199,1000)*A(1199,1000).tanh()<1
assert A(6,5)*A(6,5).tanh()>1
assert A(1199,1000).cosh()>A(9,5)
assert A(6,5).sinh()<A(151,100)
assert A(6,5).cosh()<2
assert A(1,5).exp()-1<A(222,1000)

R=F(1,5);r=F(1,2000);q=r/R
# Dottie large disk: |cos|>517/1000, |sin|<896/1000, |u|<94/100.
epsD=F(940,517);aD=F(940,1000)*F(896,517)
assert epsD<F(11,6) and aD<F(5,3)
assert (A(epsD.numerator,epsD.denominator)*A(aD.numerator,aD.denominator).exp())<10
cDlo=F(509,1000)*F(1673,1000)/F(740,1000)**2
cDhi=F(511,1000)*F(1674,1000)/F(739,1000)**2
assert cDlo>F(3,2) and cDhi<F(8,5)
# Laplace large disk: |cos|>1.356, |sin|<1.954, |u|<1.4.
assert F(14,10)/F(1356,1000)<F(11,10)
assert F(14,10)*F(1954,1000)/F(1356,1000)<F(21,10)
assert A(11,10)*A(21,10).exp()<10
assert F(1199,1000)**2-1>F(66,100)**2

def certificate(label,M,c_lower,parameter_radius,a_bound,eps_bound):
    tail=M*q**3/(1-q)
    dtail=M/R*q*q*(3-2*q)/(1-q)**2
    root_margin=c_lower*r*r-tail-parameter_radius
    critical_margin=2*c_lower*r-dtail
    assert root_margin>0 and critical_margin>0
    log_phase_deviation=a_bound*q/(1-q)+r
    multiplier_deviation=eps_bound**2*q/(1-q)
    assert multiplier_deviation<F(1,100)
    return {'label':label,'large_u_radius':str(R),'isolating_u_radius':str(r),
        'parameter_loop_radius':str(parameter_radius),'function_bound_on_large_disk':str(M),
        'quadratic_coefficient_lower_bound':str(c_lower),
        'Taylor_tail_bound':str(tail),'Taylor_derivative_tail_bound':str(dtail),
        'strict_Rouche_root_margin':str(root_margin),
        'strict_Rouche_critical_margin':str(critical_margin),
        'lifted_log_deviation_bound':str(log_phase_deviation),
        'multiplier_deviation_bound':str(multiplier_deviation),
        'conclusion':'exactly two roots in the isolating disk and exactly one critical point'}

certD=certificate('Dottie: L projection',F(10),F(3,2),F(1,10**7),F(5,3),F(11,6))
certK=certificate('Laplace: eccentricity projection',F(11,10),F(3,10),F(1,10**8),F(21,10),F(11,10))
assert F(certD['lifted_log_deviation_bound'])<F(1,200)
assert F(certK['lifted_log_deviation_bound'])<F(3,500)

# Independent symbolic recovery for the generic quadratic-normalized germ.
zz,mm=S.symbols('U mu',nonzero=True)
hh3=2*(zz*zz+3*zz+1)/(3*(zz+1)**2)
hh4=(zz**3+6*zz*zz+7*zz+1)/(3*(zz+1)**3)
cc3=hh3/mm;cc4=hh4/mm**2
rr=1-mm*cc3
ww=(24*mm*mm*cc4-22+42*rr)/(6*rr-2)
assert S.factor((1+ww)/(1-ww)-zz)==0
LL,xx=S.symbols('L x',nonzero=True)
bb=-mm*LL*(1+zz)/2
pp=-mm/(LL*zz)
translated=bb*pp*(S.exp(zz*(S.exp(-LL*xx/bb)-1))-1)
entire=mm**2*(1+zz)/(2*zz)*(S.exp(zz*(S.exp(2*xx/(mm*(1+zz)))-1))-1)
assert S.simplify(translated-entire)==0
assert S.simplify(S.diff(entire,xx).subs(xx,0)-mm)==0
assert S.simplify(S.diff(entire,xx,2).subs(xx,0)/2-1)==0

def enc(z):return {'real':mp.nstr(mp.re(z),85),'imaginary':mp.nstr(mp.im(z),85)}
def touchard(n,z):
    row=[1]
    for j in range(n):
        nxt=[0]*(len(row)+1)
        for k,val in enumerate(row):
            nxt[k]+=k*val;nxt[k+1]+=val
        row=nxt
    return sum(v*z**k for k,v in enumerate(row))

def data(u):
    ep=u/mp.cos(u);a=u*mp.tan(u);L=1j*ep*mp.exp(-a)
    P=mp.exp(a+1j*u);Q=mp.exp(a-1j*u);U=L*Q;V=-L*P;mu=-L*L*P*Q
    a2=-mu*L*(1+U)/2
    coeff={str(n):mu**(2-n)*2**(n-1)*touchard(n,U)/(factorial(n)*U*(1+U)**(n-1)) for n in [3,4]}
    return {'u':u,'epsilon':ep,'a':a,'L':L,'P':P,'Q':Q,'U':U,'V':V,'mu':mu,'a2':a2,
            'b3':coeff['3'],'b4':coeff['4']}

def run(dps):
  with mp.workdps(dps):
    d=mp.findroot(lambda z:mp.cos(z)-z,mp.mpf('.74'))
    v=mp.findroot(lambda z:z*mp.tanh(z)-1,mp.mpf('1.2'))
    RR=v/mp.cosh(v);Lstar=1j*mp.exp(-mp.sin(d))
    results=[]
    for mode,center,target_center,rho in [('Dottie',mp.mpc(d),Lstar,mp.mpf('1e-7')),
                                       ('Laplace',1j*v,1j*RR,mp.mpf('1e-8'))]:
      fun=(lambda z:1j*z/mp.cos(z)*mp.exp(-z*mp.tan(z))) if mode=='Dottie' else (lambda z:z/mp.cos(z))
      der=(lambda z:fun(z)*(1-(z/mp.cos(z))**2)/z) if mode=='Dottie' else (lambda z:(1+z*mp.tan(z))/mp.cos(z))
      target0=target_center-1j*rho
      initial_delta=mp.sqrt(rho/(abs(Lstar)*(1+mp.sin(d))/d**2)) if mode=='Dottie' else 1j*mp.sqrt(2*rho/RR)
      seeds=[center-initial_delta,center+initial_delta]
      roots=[mp.findroot(lambda z:fun(z)-target0,seed,df=der,solver='newton',tol=mp.mpf(10)**(-dps+20)) for seed in seeds]
      assert abs(roots[0]-roots[1])>mp.mpf('1e-5')
      u=roots[0];maxres=mp.mpf(0);maxdist=mp.mpf(0);samples=[];one=None
      steps=128
      for k in range(2*steps+1):
        theta=2*mp.pi*k/steps
        target=target_center-1j*rho*mp.exp(1j*theta)
        if k:
          u=mp.findroot(lambda z:fun(z)-target,u,df=der,solver='newton',tol=mp.mpf(10)**(-dps+20))
        obs=data(u)
        errs=[abs(fun(u)-target),abs(mp.exp(obs['L']*obs['Q'])-obs['P']),
              abs(mp.exp(-obs['L']*obs['P'])-obs['Q']),abs(obs['mu']-obs['epsilon']**2)]
        maxres=max(maxres,*errs);maxdist=max(maxdist,abs(u-center))
        assert abs(u-center)<mp.mpf('0.0005')
        if k%8==0:samples.append({'turn':mp.nstr(mp.mpf(k)/steps,10),**{name:enc(obs[name]) for name in ['u','L','epsilon','mu','P','Q']}})
        if k==steps:one=obs
      start=data(roots[0]);other=data(roots[1]);end=data(u)
      assert abs(one['u']-roots[1])<mp.mpf(10)**(-dps+25)
      assert abs(end['u']-roots[0])<mp.mpf(10)**(-dps+25)
      assert maxres<mp.mpf(10)**(-dps+25)
      finite_iterate_checks=[]
      for state_name,obs in [('start',start),('other',other)]:
        g=lambda z:mp.exp(obs['L']*mp.exp(-obs['L']*z))
        assert abs(mp.diff(g,obs['P'],2)/2-obs['a2'])<mp.mpf(10)**(-dps+25)
        for n in [3,4]:
          actual=mp.diff(g,obs['P'],n)/factorial(n)/obs['a2']**(n-1)
          assert abs(actual-obs['b'+str(n)])<mp.mpf(10)**(-dps+25)
        residue=1-obs['mu']*obs['b3']
        ww=(24*obs['mu']**2*obs['b4']-22+42*residue)/(6*residue-2)
        recovered_U=(1+ww)/(1-ww)
        recovered_V=obs['mu']/recovered_U
        assert abs(recovered_U-obs['U'])<mp.mpf(10)**(-dps+25)
        assert abs(recovered_V-obs['V'])<mp.mpf(10)**(-dps+25)
        xx0=mp.mpc('.001','.0007')
        normalized=xx0;original=obs['P']+xx0/obs['a2']
        closed=lambda xx:obs['mu']**2*(1+obs['U'])/(2*obs['U'])*mp.expm1(obs['U']*mp.expm1(2*xx/(obs['mu']*(1+obs['U']))))
        orbit=[];max_orbit_error=mp.mpf(0)
        for n in range(1,7):
          normalized=closed(normalized);original=g(original)
          affine_direct=obs['a2']*(original-obs['P'])
          err=abs(normalized-affine_direct);max_orbit_error=max(max_orbit_error,err)
          assert err<mp.mpf(10)**(-dps+25)
          orbit.append({'n':n,'reconstructed_normalized':enc(normalized),
                        'direct_original_affine':enc(affine_direct),'absolute_error':mp.nstr(err,8)})
        finite_iterate_checks.append({'state':state_name,'initial_normalized':enc(xx0),
          'iterates_checked':6,'maximum_error':mp.nstr(max_orbit_error,8),'orbit':orbit})
      if mode=='Dottie':
        assert mp.re(start['mu'])<1<mp.re(one['mu'])
      else:
        assert abs(start['mu']-one['mu'])<mp.mpf(10)**(-dps+25)
        assert abs(start['L'])<mp.e*RR<abs(one['L'])
      results.append({'projection':mode,'steps_per_turn':steps,'turns':2,
        'root_exchange_error':mp.nstr(abs(one['u']-roots[1]),8),
        'two_turn_return_error':mp.nstr(abs(end['u']-roots[0]),8),
        'max_identity_residual':mp.nstr(maxres,8),'max_u_distance':mp.nstr(maxdist,35),
        'start':{key:enc(start[key]) for key in start},
        'after_one_turn':{key:enc(one[key]) for key in one},
        'after_two_turns':{key:enc(end[key]) for key in end},'trajectory':samples,
        'finite_iterate_checks':finite_iterate_checks})
    return {'decimal_precision':dps,'Dottie_d':mp.nstr(d,85),'Laplace_v':mp.nstr(v,85),'loops':results}

rows=[run(110),run(190)]
for j in range(2):
    for state in ['start','after_one_turn','after_two_turns']:
        for key in rows[0]['loops'][j][state]:
            for part in ['real','imaginary']:
                with mp.workdps(100):
                    assert abs(mp.mpf(rows[0]['loops'][j][state][key][part])-mp.mpf(rows[1]['loops'][j][state][key][part]))<mp.mpf('1e-80')
    for state_index in range(2):
        for orbit_index in range(6):
            for part in ['real','imaginary']:
                with mp.workdps(100):
                    left=rows[0]['loops'][j]['finite_iterate_checks'][state_index]['orbit'][orbit_index]['reconstructed_normalized'][part]
                    right=rows[1]['loops'][j]['finite_iterate_checks'][state_index]['orbit'][orbit_index]['reconstructed_normalized'][part]
                    assert abs(mp.mpf(left)-mp.mpf(right))<mp.mpf('1e-80')
out={'status':'all rational/Arb certificates and independent two-precision loop/germ checks passed',
     'certified_scope':'local two-sheet root count, unique simple critical point, phase/germ analytic domains, monodromy for every loop with winding number one in each stated parameter disk',
     'numerical_scope':'two counterclockwise circular turns, 128 steps per turn, 110/190 decimal digits, 80-place agreement',
     'generic_germ_field_identity':'Q(mu,c3,c4)=Q(U,V), U=LQ, V=-LP; U!=0,-1 and mu!=0',
     'entire_map_reconstruction':'G(x)=mu^2*(1+U)/(2U)*expm1(U*expm1(2x/(mu*(1+U))))',
     'certificates':[certD,certK],'runs':rows}
(HERE/'monodromy-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'status':out['status'],'certificates':out['certificates'],
       'loops':[{'precision':row['decimal_precision'],'cases':[{**{k:v for k,v in c.items() if k not in ['start','after_one_turn','after_two_turns','trajectory','finite_iterate_checks']},
          'finite_iterate_max_errors':[b['maximum_error'] for b in c['finite_iterate_checks']]} for c in row['loops']]} for row in rows]},indent=2))
