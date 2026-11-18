"""Independent symbolic review of reciprocal/Dottie normalization and fields."""
from pathlib import Path
import json
import sympy as S
from sympy.functions.combinatorial.numbers import stirling

OUT=Path(__file__).resolve().parent
a,L,p,x,z,s,t=S.symbols('a L p x z s t',nonzero=True)
T=lambda n,w:sum(stirling(n,k,kind=2)*w**k for k in range(n+1))
h=lambda n:S.factor(2**(n-1)*T(n,a)/(S.factorial(n)*a*(1+a)**(n-1)))
h3,h4=h(3),h(4)
rho=S.factor(1-h3)
theta=a+1/a
assert S.factor(rho-theta/(3*(theta+2)))==0
assert S.factor(6*rho-2+4*a/(1+a)**2)==0
w=S.factor((24*h4-22+42*rho)/(6*rho-2))
assert S.factor(w-(a-1)/(a+1))==0
assert S.factor((1+w)/(1-w)-a)==0

# Exact parabolic compatibility: q abbreviates exp(a-1/a), then its defining
# equation gives q=-1/a^2. The checks keep this one substitution explicit.
p_compat=S.exp(a);L_compat=-S.exp(-a)/a
compatibility=a*a*S.exp(a-1/a)+1
assert S.simplify(L_compat*p_compat+1/a)==0
phase_residual=S.simplify(L_compat*S.exp(-L_compat*p_compat)-a)
assert S.simplify(phase_residual+compatibility/(a*S.exp(a-1/a)))==0
q=S.symbols('q',nonzero=True)
assert S.simplify((-1/(a*q)-a).subs(q,-1/a**2))==0
assert S.simplify((-1/(a*a*q)).subs(q,-1/a**2)-1)==0
assert S.simplify(compatibility.subs(a,1))==2
assert S.simplify(compatibility.subs(a,-1))==2

# Exact affine conjugacy, with the parabolic fixed-point equation p L a=-1.
a2=-L*(1+a)/2
normalized=a2*p*(S.exp(a*(S.exp(-L*x/a2)-1))-1)
normalized=normalized.subs(p,-1/(L*a))
F=(1+a)/(2*a)*(S.exp(a*(S.exp(2*x/(1+a))-1))-1)
assert S.simplify(normalized-F)==0
beta=2/(1+a); affine_A=(1+a)*S.exp(-a)/(2*a);affine_B=-(1+a)/(2*a)
two_stage=affine_A*S.exp(a*S.exp(beta*x))+affine_B
assert S.simplify(two_stage-F)==0
F0=(S.exp(2*x)-1)/2
assert S.simplify(S.limit(F,a,0)-F0)==0
reduced_map_degrees={}
for n in (3,4):
    numerator,denominator=S.fraction(S.cancel(h(n)))
    assert S.Poly(S.gcd(numerator,denominator),a).degree()==0
    degree=max(S.degree(numerator,a),S.degree(denominator,a))
    assert degree==n-1
    reduced_map_degrees[str(n)]=int(degree)
coefficients=[]
N=14
inner=[S.Rational(0)]+[1/S.factorial(k) for k in range(1,N+1)]
power=[S.Rational(1)]+[S.Rational(0)]*N
powers=[power]
for k in range(1,N+1):
    power=[sum(power[j]*inner[i-j] for j in range(i+1)) for i in range(N+1)]
    powers.append(power)
for n in range(1,15):
    # Independent nested-composition coefficient extraction uses powers of the
    # inner exponential through n, with no complete expression-series shortcut.
    coeff=sum(a**k*powers[k][n]/S.factorial(k) for k in range(1,n+1))
    coeff=S.factor((1+a)/(2*a)*(2/(1+a))**n*coeff)
    assert S.factor(coeff-h(n))==0
    assert S.simplify(S.limit(h(n),a,0)-2**(n-1)/S.factorial(n))==0
    num,den=S.fraction(h(n))
    if n>=3:
        assert S.factor(S.diff(h(n),a))!=0
        tp=S.Poly(T(n,a)/a,a)
        assert tp.LC()==1
        assert tp.coeff_monomial(a**(n-2))==n*(n-1)//2
    coefficients.append({'n':n,'h_n':str(h(n))})
assert h(1)==1 and h(2)==1

# Reciprocal quotient and real/complex quadratic fields at Dottie.
assert S.factor(rho.subs(a,1/a)-rho)==0
assert S.factor(h3.subs(a,1/a)-h3)==0
assert S.factor(h4.subs(a,1/a)-h4)!=0
assert S.factor((a*a-2*s*a+1).subs(s,(a+1/a)/2))==0
disc_real=S.discriminant(t*t-(1-s*s),t)
disc_phase=S.discriminant(t*t-2*s*t+1,t)
assert S.expand(disc_real-4*(1-s*s))==0
assert S.expand(disc_phase-4*(s*s-1))==0
assert S.degree(S.gcd(1-s*s,S.diff(1-s*s,s)),s)==0

# ODE and Touchard identities by independent differentiation.
W=L*S.exp(-L*z);G=S.exp(W)
exponents=S.Matrix([-L*z,W]);jacobian=exponents.jacobian([L,z])
assert S.simplify(jacobian.det()-L*S.exp(-L*z))==0
assert S.simplify(G*S.diff(G,z,2)-S.diff(G,z)**2+L*G*S.diff(G,z))==0
for n in range(0,9):
    assert S.simplify(S.diff(G,z,n)-(-L)**n*T(n,W)*G)==0

result={'status':'independent symbolic checks passed',
 'sympy_version':S.__version__,
 'normalized_domain':'alpha nonzero and alpha not equal to -1; L nonzero; p L alpha=-1',
 'a2':str(a2),'h3':str(h3),'h4':str(h4),'rho':str(rho),
 'parabolic_compatibility':str(compatibility)+' = 0',
 'parabolic_reconstruction':{'p':str(p_compat),'L':str(L_compat)},
 'compatibility_checks':['forward residual factorization','converse phase substitution',
 'multiplier-one substitution','alpha=1 excluded','alpha=-1 excluded'],
 'recovery_w':str(w),'denominator_6rho_minus_2':str(S.factor(6*rho-2)),
 'independent_composition_coefficients_checked_through':14,
 'touchard_derivatives_checked_through':8,
 'two_stage_affine_decomposition':'exactly verified',
 'affine_tower_scope':'arbitrary nonzero A_j and c_j, arbitrary B_j; analytical Ax induction',
 'reduced_rational_map_degrees':reduced_map_degrees,
 'alpha_zero_limit':str(F0),
 'alpha_zero_coefficient_limits_checked_through':14,
 'jacobian_determinant':str(S.simplify(jacobian.det())),
 'coefficients':coefficients,
 'quadratic_discriminants':{'real_phase_field':str(S.factor(disc_real)),
                             'complex_phase_field':str(S.factor(disc_phase))},
 'analytical_reviews':['Ax induction includes common constant field and derivative rank',
 'Dottie coefficient transcendence uses nonconstant rational maps over Q',
 'quadratic field degrees follow squarefree 1-s^2 and real/nonreal fields',
 'two-logarithm Schanuel conclusions retain their exact hypothesis']}
(OUT/'independent-checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(json.dumps({k:v for k,v in result.items() if k!='coefficients'},indent=2))
