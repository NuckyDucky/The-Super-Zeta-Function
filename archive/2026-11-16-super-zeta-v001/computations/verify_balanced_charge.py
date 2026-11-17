"""Headless charge-projected reciprocal IFS and prime-clock checks.

Python + mpmath + python-flint. Exact integers/Fractions, 130-digit points,
and a new directed four-branch invariant-disk certificate at 768 bits.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
from functools import cache
from math import comb, factorial
import json
import time
import mpmath as mp
from flint import arb,acb,ctx

HERE=Path(__file__).resolve().parent
mp.mp.dps=130
ctx.prec=768
CHARGES=((1,0),(-1,0),(0,1),(0,-1))


def ar(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator


def four_branch_certificate():
    lo,hi=Fraction(73,100),Fraction(74,100)
    for _ in range(600):
        mid=(lo+hi)/2
        test=ar(mid).cos()-ar(mid)
        if test>0:lo=mid
        elif test<0:hi=mid
        else:raise ArithmeticError('unresolved directed Dottie bisection')
    d=arb(ar((lo+hi)/2),ar((hi-lo)/2))
    y=(-d.sin()).exp();L=acb(0,y)
    c=acb(ar(Fraction(-37,2)),32);R=arb(20)
    rminus=abs(c)-R;rplus=abs(c)+R
    M=rplus.log()+arb.pi()
    q=1/(y*rminus*(2*arb.pi()*1000000-M))
    assert q<ar(Fraction(1,50000000))
    centers=[];margins=[]
    for j in range(4):
        b=-(((c.log()+acb(0,2*arb.pi()*1000000))/L).log()+acb(0,2*arb.pi()*j))/L
        margin=R-abs(b-c)-R*q
        assert margin>1
        centers.append(str(b));margins.append(str(margin))
    separation=2*arb.pi()/y-2*R*q
    assert separation>12
    lower=(y*12).exp()
    assert lower>rplus
    return {'arb_bits':ctx.prec,'dottie_bracket':[str(lo),str(hi)],
            'L':'i*exp(-sin(d)), d=cos(d)',
            'disk_center':['-37/2','32'],'disk_radius':'20',
            'inner_log_k':1000000,'outer_log_j':[0,1,2,3],
            'inverse_centers':centers,'uniform_derivative_bound':str(q),
            'rational_derivative_upper':'1/50000000',
            'invariance_margins':margins,'image_radius_fraction_upper':'19/20',
            'image_separation_lower':str(separation),
            'physical_image_modulus_lower':str(lower),
            'physical_image_disjoint_from_disk':True}


def charge_walks(max_steps=24,weights=(1,1,1,1)):
    dist={(0,0):1};ret=[1]
    for _ in range(max_steps):
        nxt={}
        for (x,y),v in dist.items():
            for (dx,dy),w in zip(CHARGES,weights):
                pos=(x+dx,y+dy)
                nxt[pos]=nxt.get(pos,0)+v*w
        dist=nxt;ret.append(dist.get((0,0),0))
    return ret


def moment(m,a,b):
    if m%2:return a*0
    n=m//2
    return factorial(2*n)*sum(a**(2*j)*b**(2*(n-j))/
           (factorial(j)**2*factorial(n-j)**2) for j in range(n+1))/4**n


def exact_checks():
    returns=charge_walks()
    assert all(returns[m]==(0 if m%2 else comb(m,m//2)**2) for m in range(25))
    weighted=charge_walks(20,(1,1,2,2))
    assert all(weighted[m]==moment(m,Fraction(2),Fraction(4)) for m in range(21))
    clocks=[]
    for p in (2,3,5):
        for k in range(4):
            m=p**k
            counts=[m*returns[j] if j%m==0 else 0 for j in range(1,25)]
            # Direct origin/clock-zero propagation in Z² x C_m.
            dist={(0,0,0):1};actual=[]
            for j in range(1,25):
                nxt={}
                for (x,y,a),v in dist.items():
                    for dx,dy in CHARGES:
                        pos=(x+dx,y+dy,(a+1)%m)
                        nxt[pos]=nxt.get(pos,0)+v
                dist=nxt;actual.append(m*dist.get((0,0,0),0))
            assert counts==actual
            clocks.append({'prime':p,'level':k,'clock_length':m,
                           'exact_fixed_trace_counts_1_to_24':counts})
    return {'return_counts_0_to_24':returns,'anisotropic_integer_weights':[1,1,2,2],
            'anisotropic_returns_0_to_20':weighted,'prime_clock_checks':clocks}


@cache
def quartet(n):
    def F(t):
        th=mp.acos(-t/mp.sinh(t))
        return th+mp.cosh(t)*mp.sin(th)
    target=(n+mp.mpf('.5'))*mp.pi
    t=mp.findroot(lambda t:F(t)-target,
                  (mp.log(2*mp.pi*n),mp.log(2*mp.pi*n)+mp.mpf('.15')))
    return t,mp.acos(-t/mp.sinh(t))


def point_checks():
    green=[]
    for a,b,z in ((mp.mpf('.5'),mp.mpf('.5'),mp.mpf('.2')),
                  (mp.mpf(2),mp.mpf(3),mp.mpf('.02')),
                  (mp.mpc('1','.3'),mp.mpc('-.2','.8'),mp.mpc('.02','.01'))):
        series=sum(moment(m,a,b)*z**m for m in range(161))
        D=1-z*z*(a-b)**2
        value=2/mp.pi/mp.sqrt(D)*mp.ellipk(4*a*b*z*z/D)
        error=abs(series-value)
        r=abs(z)*(abs(a)+abs(b))
        tail=r**161/(1-r)
        assert error<mp.mpf('1e-120')+tail
        green.append({'a':str(a),'b':str(b),'z':str(z),
                       'elliptic_moment_series_error':mp.nstr(error,25),
                       'geometric_series_tail_bound':mp.nstr(tail,25)})
    heat=[]
    for n,s in ((1,mp.mpf('.4')),(2,mp.mpc('.3','.1')),(5,mp.mpf('.2'))):
        t,th=quartet(n)
        series=sum(s**m*moment(m,t,1j*th)/factorial(m) for m in range(121))
        target=mp.besseli(0,s*t)*mp.besselj(0,s*th)
        A=abs(s)*(t+th)
        bound=mp.exp(A)*A**121/factorial(121)
        error=abs(series-target)
        assert error<bound+mp.mpf('1e-120')
        heat.append({'quartet':n,'s':str(s),'Bessel_heat_error':mp.nstr(error,25),
                     'exponential_Taylor_bound':mp.nstr(bound,25)})
    return {'anisotropic_Green_checks':green,'charge_projected_heat_checks':heat}


def actual_ifs_checks():
    d=mp.findroot(lambda x:mp.cos(x)-x,mp.mpf('.739'))
    L=1j*mp.exp(-mp.sin(d));c=mp.mpc('-18.5','32')
    def branch(w,j):return -(mp.log((mp.log(w)+2000000j*mp.pi)/L)+2j*mp.pi*j)/L
    def derivative(w):return -1/(L*w*(mp.log(w)+2000000j*mp.pi))
    t,th=quartet(1)
    rows=[]
    for length in range(1,5):
        traces={label:[mp.mpc(0),mp.mpc(0)] for label in ('isotropic','quartet1')}
        count=0
        for word in product(range(4),repeat=length):
            charge=tuple(sum(CHARGES[j][q] for j in word) for q in (0,1))
            if charge!=(0,0):continue
            count+=1
            def B(w):
                db=mp.mpc(1)
                for j in reversed(word):
                    db*=derivative(w);w=branch(w,j)
                return w,db
            w=c
            for _ in range(19):w,_=B(w)
            value,db=B(w)
            assert abs(value-w)<mp.mpf('1e-115')
            for label,weights in (('isotropic',[mp.mpf('.25')]*4),
                                  ('quartet1',[t/2,t/2,1j*th/2,1j*th/2])):
                weight=mp.fprod(weights[j] for j in word)
                traces[label][0]+=weight/(1-db)
                traces[label][1]+=weight*db/(1-db)
        checks=[]
        for label,a,b in (('isotropic',mp.mpf('.5'),mp.mpf('.5')),
                          ('quartet1',t,1j*th)):
            target=moment(length,a,b)
            error=abs(traces[label][0]-traces[label][1]-target)
            assert error<mp.mpf('1e-115')
            checks.append({'weights':label,'trace0':mp.nstr(traces[label][0],45),
                            'trace1':mp.nstr(traces[label][1],45),
                            'supertrace_error':mp.nstr(error,25)})
        rows.append({'word_length':length,'balanced_words':count,'checks':checks})
    return rows


def controlled_balanced_Q():
    # Proved uniform bound: exp(|s|(t_n+theta_n))<320*n for |s|<=1.
    p,N,K,J=2,64,4,40
    Z,r,h=Fraction(1,1000),Fraction(1,4),Fraction(1,4)
    A=Fraction(2,25)
    assert 320*Z*r==A
    tail_n=320*Z*r**(N+1)*((N+1)-N*r)/(1-r)**2/(1-A)**2
    tail_k=N*A**(p**(K+1))/(1-A)**2
    tail_j=N*(K+1)*A**(J+1)/((J+1)*(1-A))
    omitted=Fraction(0);log_value=mp.mpf(0);evaluations=0
    def mpr(q):return mp.mpf(q.numerator)/q.denominator
    for n in range(1,N+1):
        t,th=quartet(n)
        for k in range(K+1):
            m=p**k
            qbound=320*Z*n*r**n*h**k
            step_bound=qbound**m
            for j in range(1,J+1):
                power=m*j
                bound=step_bound**j/j
                if bound<Fraction(1,10**105):
                    # The remaining geometric tail is less than twice this
                    # fixed rational threshold, since step_bound<=A<1/2.
                    omitted+=Fraction(2,10**105);break
                x=mpr(Z*r**n*h**k)
                log_value-=x**power/j*mp.besseli(0,power*t)*mp.besselj(0,power*th)
                evaluations+=1
    error=tail_n+tail_k+tail_j+omitted
    assert error<Fraction(1,2)
    return {'p':p,'z':str(Z),'rho':str(r),'eta':str(h),'s':1,
            'quartet_count':N,'max_clock_level':K,'max_log_index':J,
            'Bessel_terms_evaluated':evaluations,
            'log_partial_sum':mp.nstr(log_value,100),
            'partial_Q_bal':mp.nstr(mp.exp(log_value),100),
            'absolute_log_tail_bound_exact':str(error),
            'relative_product_error_bound_exact':str(2*error),
            'relative_product_error_bound_decimal':mp.nstr(2*mpr(error),40),
            'bound_arithmetic':'exact Fractions; partial Bessel evaluations at130 decimal digits'}


def main():
    start=time.perf_counter()
    result={'precision':{'mpmath_dps':mp.mp.dps,'arb_bits':ctx.prec},
            'four_branch_certificate':four_branch_certificate(),
            'exact_lattice_checks':exact_checks(),
            'point_kernel_checks':point_checks(),
            'actual_holomorphic_IFS_checks':actual_ifs_checks(),
            'controlled_balanced_joint_product':controlled_balanced_Q(),
            'passed':True}
    result['elapsed_seconds']=time.perf_counter()-start
    path=HERE/'balanced-charge-results.json'
    path.write_text(json.dumps(result,indent=2),encoding='utf-8')
    print('PASS: four-branch certificate, lattice/clock traces, elliptic/Bessel kernels, actual IFS supertraces and controlled joint product.')
    print('Seconds:',round(result['elapsed_seconds'],3))
    print(path)


if __name__=='__main__':main()
