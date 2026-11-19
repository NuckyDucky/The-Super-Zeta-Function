"""Exact and directed checks of the cosine/quartet Fredholm spectrum.

CPU only. No application import or contact. SymPy exact algebra, mpmath points,
and directed python-flint Acb integrals with analytic branch handling.
"""
from pathlib import Path
from fractions import Fraction
import json
import time
import mpmath as mp
import sympy as sy
from flint import arb,acb,ctx

HERE=Path(__file__).resolve().parent
mp.mp.dps=140
ctx.prec=512


def exact_traces():
    a,x=sy.symbols('a x')
    N=12
    c=[sy.Integer(1),-(1+a)]+[sy.Rational((-1)**m*2**(2*m-1),sy.factorial(2*m)) for m in range(2,N+1)]
    traces=[]
    for n in range(1,N+1):
        pn=sy.expand(-n*c[n]-sum(c[j]*traces[n-j-1] for j in range(1,n)))
        traces.append(pn)
    actual=[sy.factor(p.subs(a,1)) for p in traces]
    assert actual[:4]==[sy.Integer(2),sy.Rational(10,3),sy.Rational(92,15),sy.Rational(3538,315)]
    pr,qr,X=sy.symbols('pr qr X',nonzero=True)
    quartet=sy.prod(X-pr**sigma*qr**tau for sigma in (-1,1) for tau in (-1,1))
    e1=(pr+1/pr)*(qr+1/qr)
    e2=pr**2+pr**(-2)+qr**2+qr**(-2)+2
    assert sy.cancel(quartet-(X**4-e1*X**3+e2*X**2-e1*X+1))==0
    checks=[]
    z=sy.symbols('z')
    for n in (2,4,6):
        B=sy.zeros(n+1)
        for j in range(n):
            for k in range(n):B[j,k]=sy.I*sy.sign(j-k)/n
            B[j,n]=a
            B[n,j]=-sy.I*(-1 if j<n//2 else 1)/n
        B[n,n]=a
        C=((1+sy.I*z/n)**n+(1-sy.I*z/n)**n)/2
        Q=(1+z*z/n**2)**(n//2)
        got=(sy.eye(n+1)-z*B).det(method='domain-ge')
        assert sy.cancel(got-C+a*z*Q)==0
        assert sy.simplify(sy.trace(B**2)-(1+a*a-sy.Rational(1,n)))==0
        checks.append({'even_cells':n,'exact_characteristic':str(sy.factor(got)),
                       'exact_trace_square':str(sy.trace(B**2))})
    return {'a':'epsilon^(-2) for traces; epsilon^(-1) in finite matrix checks',
            'trace_polynomials':[str(sy.factor(p)) for p in traces],
            'epsilon1_rational_traces':[str(p) for p in actual],
            'exact_quartet_polynomial':str(X**4-e1*X**3+e2*X**2-e1*X+1),
            'exact_finite_matrices':checks}


def phase_roots(N=128):
    d=mp.findroot(lambda u:mp.cos(u)-u,mp.mpf('.74'))
    rows=[];roots=[];worst=mp.mpf(0)
    for n in range(1,N+1):
        def equation(t):
            th=mp.acos(-t/mp.sinh(t))
            return th+mp.cosh(t)*mp.sin(th)-(n+mp.mpf('.5'))*mp.pi
        t=mp.findroot(equation,(mp.log(2*mp.pi*n),mp.log(2*mp.pi*n)+mp.mpf('.1')))
        th=mp.acos(-t/mp.sinh(t));u=mp.cosh(t)*mp.sin(th)+1j*t
        sigma=(-1)**n
        alpha=mp.exp(t+1j*th)
        L=-mp.exp(-alpha)/alpha
        errors=[abs(mp.cos(u)-sigma*u),abs(alpha-(sigma*mp.sin(u)+1j*u)),
                abs(1/alpha-(sigma*mp.sin(u)-1j*u)),
                abs(L-sigma*1j*mp.exp(-sigma*mp.sin(u)))]
        worst=max(worst,*errors)
        assert max(errors)<mp.mpf('1e-128')
        hh=t/mp.tanh(t);qg=mp.sqrt(mp.sinh(t)**2-t*t)
        coefficients=[1,4*hh,4*(hh*hh+qg*qg)+2,4*hh,1]
        for aa in (alpha,1/alpha,mp.conj(alpha),1/mp.conj(alpha)):
            assert abs(mp.polyval(coefficients,aa))/(1+abs(aa)**4)<mp.mpf('1e-128')
        roots.append(u)
        if n<=8:rows.append({'n':n,'u':[mp.nstr(u.real,100),mp.nstr(u.imag,100)],
                            'cosine_sign':sigma,'alpha':[mp.nstr(alpha.real,75),mp.nstr(alpha.imag,75)],
                            'maximum_point_residual':mp.nstr(max(errors),20)})
    tracechecks=[]
    for m in range(1,7):
        value=d**(-2*m)+2*mp.re(sum(u**(-2*m) for u in roots))
        bound=2*mp.pi**(-2*m)/(2*m-1)*(N-mp.mpf('.5'))**(1-2*m)
        target=mp.mpf(exact_traces_cache['epsilon1_rational_traces'][m-1])
        assert abs(value-target)<bound
        tracechecks.append({'m':m,'partial_sum':mp.nstr(value,70),
                            'exact_target':exact_traces_cache['epsilon1_rational_traces'][m-1],
                            'rigorous_analytic_tail_bound':mp.nstr(bound,40)})
    return {'scope':'140-digit point roots; analytic full-spectrum tail bound',
            'number_of_nonunit_quartets':N,'dottie':mp.nstr(d,110),
            'first_representatives':rows,'maximum_point_residual':mp.nstr(worst,30),
            'trace_sum_checks':tracechecks}


def projection_checks():
    rows=[]
    for eps in (mp.mpf('.5'),mp.mpf(1),mp.mpf(2)):
        for z in (mp.mpf('.4'),mp.mpc('.3','.2'),mp.mpc('-.2','.35')):
            radius=arb('1/2');ez=acb(str(z.real),str(z.imag));ae=arb(str(eps))
            for N in (16,64,256,4096):
                C=((1+1j*ez/N)**N+(1-1j*ez/N)**N)/2
                Q=(1+ez**2/N**2)**(N//2)
                delta=C-ez/ae*Q
                delta_minus=C+ez/ae*Q
                approx=(-ez**2/N).exp()*delta*delta_minus
                exact=ez.cos()**2-ez**2/ae**2
                eta=radius**3/(3*N*N*(1-radius/N))
                eta2=radius**4/(4*N**3*(1-radius**2/N**2))
                error=radius.exp()*(eta.exp()-1)+radius/ae*(eta2.exp()-1)
                bound=error*(2*(radius.exp()+radius/ae)+error)
                assert abs(approx-exact)<bound
                rows.append({'epsilon':str(eps),'z':[str(z.real),str(z.imag)],'N':N,
                             'directed_error':str(abs(approx-exact)),
                             'analytic_directed_upper_bound':str(bound),'passed':True})
    return rows


def acb_integral_quarter(s,epsilon):
    """Certified relative Mellin integral for s in quarter-integers <1.

    x=q^4 on [0,1] removes endpoint powers. 2F1(1,1;2;-z) evaluates
    log(1+z)/z including its removable value at zero. The analytic callback
    verifies a positive-real-part logarithm argument on complex input balls.
    """
    ss=arb(str(s.numerator))/s.denominator;ee=arb(str(epsilon))
    exponent=7-8*s
    assert exponent.denominator==1 and exponent>=0
    exponent=int(exponent)
    def low(q,analytic):
        X=q**4;sech2=1/X.cosh()**2
        Z=q**8*sech2/ee**2
        if analytic and not ((1+Z).real>0):return acb('nan')
        ratio=(-Z).hypgeom_2f1(1,1,2)
        return 8*q**exponent*sech2/ee**2*ratio
    def high(x,analytic):
        logx=x.log(analytic=analytic)
        v=x*x/x.cosh()**2/ee**2
        if analytic and not ((1+v).real>0):return acb('nan')
        return 2*((-2*ss-1)*logx).exp()*v.log1p()
    tol=arb(2)**(-300)
    total=acb.integral(low,0,1,abs_tol=tol,rel_tol=tol,eval_limit=20000)
    for left,right in ((1,4),(4,12),(12,40),(40,120)):
        total+=acb.integral(high,left,right,abs_tol=tol,rel_tol=tol,eval_limit=20000)
    T=arb(120);power=1-2*ss
    denom=2-power/T if power>0 else arb(2)
    tail=8/ee**2*T**power*(-2*T).exp()/denom
    assert total.is_finite()
    # Real integrand and positive tail: a symmetric enclosure is retained.
    val=arb(total.real,tail)
    assert val>0
    return val,tail


def mellin_checks():
    rows=[]
    for eps in ('1','2'):
        for s in (Fraction(-3,4),Fraction(-1,4),Fraction(0),Fraction(1,4),Fraction(3,4)):
            integral,tail=acb_integral_quarter(s,eps)
            ss=arb(s.numerator)/s.denominator;pi=arb.pi()
            J=ss*(pi*ss).sin()/pi*integral
            if s==0:
                value=arb(0);curvature=2*integral
            else:
                base=2*(-2*ss*pi.log()).exp()*((2*ss*arb(2).log()).exp()-1)*(2*ss).zeta()
                value=base+J;curvature=None
            rows.append({'epsilon':eps,'s':str(s),'relative_Mellin_integral':str(integral),
                         'integral_absolute_tail_bound_after_x120':str(tail),
                         'entire_correction':str(J),'spectral_zeta':str(value),
                         'relative_second_derivative_at_zero':str(curvature) if curvature is not None else None})
    # Independent point quadrature at a lower precision and matching branch.
    with mp.workdps(70):
        for row in rows:
            if row['s'] not in ('1/4','-1/4'):continue
            s=mp.mpf(row['s']);eps=mp.mpf(row['epsilon'])
            fun=lambda x:2*x**(-2*s-1)*mp.log1p(x*x/mp.cosh(x)**2/eps**2) if x else mp.mpf(0)
            I=mp.quad(fun,[0,1,4,12,40,120])
            # The independent 70-digit point lies within a 1e-65 inflation of
            # the much tighter directed enclosure; it has its own point scope.
            directed=arb(row['relative_Mellin_integral'])
            assert abs(arb(mp.nstr(I,68))-directed)<arb('1e-64')
            row['independent_70dps_integral']=mp.nstr(I,65)
    return rows


def main():
    global exact_traces_cache
    start=time.perf_counter();exact_traces_cache=exact_traces()
    out={'precision':{'mpmath_dps':mp.mp.dps,'arb_bits':ctx.prec},
         'exact_algebra':exact_traces_cache,'phase_recovery':phase_roots(),
         'directed_finite_projection_checks':projection_checks(),
         'directed_Mellin_checks':mellin_checks(),
         'zeta_normalization':{'value_at_zero':'0','derivative_at_zero':'-log(4)',
                               'zeta_regularized_determinant':'4',
                               'pole':'s=1/2, residue 1/pi',
                               'trivial_zeros':'s=0,-1,-2,...'},
         'elapsed_seconds':time.perf_counter()-start,'passed':True}
    (HERE/'cosine-spectrum-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('PASS: exact finite determinants/traces, 128 phase roots, 36 projection bounds, 10 directed Mellin integrals.')
    print('Elapsed seconds:',out['elapsed_seconds'])


if __name__=='__main__':main()
