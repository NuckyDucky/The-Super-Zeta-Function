"""Balanced signed histories: primitive counts and certified (++--) fold.

Dependencies: mpmath and python-flint. Headless CPU only. The retained
proof is research/ordered-signed-histories.md.
"""
from pathlib import Path
from fractions import Fraction
from itertools import combinations, product
from math import comb
import json
import time
import mpmath as mp
from flint import arb, acb, ctx
HERE=Path(__file__).resolve().parent
ctx.prec=1024;mp.mp.dps=220

def mobius(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign

def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def primitive(w):
    return all(w!=w[:d]*(len(w)//d) for d in divisors(len(w)) if d<len(w))
def necklace(w):return min(w[j:]+w[:j] for j in range(len(w)))
def balanced_words(n):
    for positions in combinations(range(2*n),n):
        plus=set(positions)
        yield tuple(1 if j in plus else -1 for j in range(2*n))

def exp_coefficients(logarithm,N):
    out=[Fraction(1)]+[Fraction(0)]*N
    for n in range(1,N+1):
        out[n]=sum((k*logarithm[k]*out[n-k] for k in range(1,n+1)),Fraction(0))/n
    return out

def euler_coefficients(primitives,N):
    out=[1]+[0]*N
    for k in range(1,N+1):
        p=primitives[k]
        factor=[comb(p+j-1,j) if p else int(j==0) for j in range(N//k+1)]
        nxt=[0]*(N+1)
        for i,a in enumerate(out):
            for j,b in enumerate(factor):
                if i+k*j<=N:nxt[i+k*j]+=a*b
        out=nxt
    return out

def counts():
    N=12;rows=[];ps={1:[0],2:[0]}
    for n in range(1,N+1):
        row={'n':n,'balanced_single_count':comb(2*n,n),
             'balanced_pair_count':comb(2*n,n)**2}
        for r in [1,2]:
            numerator=sum(mobius(d)*comb(2*n//d,n//d)**r for d in divisors(n))
            assert numerator%(2*n)==0
            p=numerator//(2*n);ps[r].append(p)
            row[f'primitive_necklaces_{r}_streams']=p
        anti=sum(mobius(d)*2**(n//d) for d in divisors(n) if d%2)
        assert anti%(2*n)==0
        row['primitive_complementary_half_necklaces']=anti//(2*n)
        if n<=6:
            brute={necklace(w) for w in balanced_words(n) if primitive(w)}
            assert len(brute)==ps[1][n]
        if n<=4:
            words=list(balanced_words(n));pairset=set()
            for w,v in product(words,repeat=2):
                paired=tuple((a+1)+(b+1)//2 for a,b in zip(w,v))
                if primitive(paired):pairset.add(necklace(paired))
            assert len(pairset)==ps[2][n]
        if n<=8:
            anti_set=set()
            for v in product([-1,1],repeat=n):
                w=v+tuple(-a for a in v)
                if primitive(w):anti_set.add(necklace(w))
            assert len(anti_set)==anti//(2*n)
        rows.append(row)
    for r in [1,2]:
        logs=[Fraction(0)]+[Fraction(comb(2*n,n)**r,2*n) for n in range(1,N+1)]
        ee=exp_coefficients(logs,N)
        assert ee==euler_coefficients(ps[r],N)
        if r==1:assert ee==[Fraction(comb(2*n,n),n+1) for n in range(N+1)]
    return rows

def fold_mp(x,t,y):
    z=mp.mpc(x,t);L=1j*y;a=mp.exp(L*z);b=mp.exp(L*a);dd=L*L*a*b
    return mp.re(b-mp.conj(z)),mp.im(b-mp.conj(z)),abs(dd)**2-1

def fold_arb(x,t,y):
    z=acb(x,t);L=acb(0,y);a=(L*z).exp();b=(L*a).exp();dd=L*L*a*b
    hy=acb(0,1)*a*b*(1+L*z)
    d_z=dd*L*(1+L*a)
    d_y=dd*(2/y+acb(0,1)*z+acb(0,1)*a*(1+L*z))
    fun=[b.real-x,b.imag+t,abs(dd)**2-1]
    jac=[[dd.real-1,-dd.imag,hy.real],
         [dd.imag,dd.real+1,hy.imag],
         [2*(dd.conjugate()*d_z).real,
          2*(dd.conjugate()*acb(0,1)*d_z).real,
          2*(dd.conjugate()*d_y).real]]
    return fun,jac

def orbit_arb(z,L,word):
    zz=[z];dd=[acb(1)]
    for s in word:
        zz.append((s*L*zz[-1]).exp())
        dd.append(dd[-1]*s*L*zz[-1])
    S1=sum((word[j]*dd[j] for j in range(len(word))),acb(0))
    S2=sum((dd[j]**2 for j in range(len(word))),acb(0))
    rho=S2/(3*S1*S1)
    action=sum((word[j]*L*zz[j] for j in range(len(word))),acb(0))
    return zz,dd,rho,S1,action

def certify_fold():
    guess=(mp.mpf('.09081518944588625'),mp.mpf('-.899976732173257'),
           mp.mpf('.75019697231646185'))
    root=mp.findroot(fold_mp,guess,maxsteps=30,tol=mp.mpf('1e-205'))
    strings=[mp.nstr(a,180) for a in root]
    center=[arb(a) for a in strings];radius=arb('1e-140')
    box=[arb(a,radius) for a in strings]
    fc,jc=fold_arb(*center);fb,jb=fold_arb(*box)
    center_mp=[mp.mpf(a) for a in strings]
    jac_errors=[]
    for i in range(3):
        for j in range(3):
            def component(v):
                values=list(center_mp);values[j]=v
                return fold_mp(*values)[i]
            independent=mp.diff(component,center_mp[j])
            jac_errors.append(abs(independent-mp.mpf(jc[i][j].mid()._mpf_)))
    assert max(jac_errors)<mp.mpf('1e-210')
    inverse=mp.inverse(mp.matrix([[mp.mpf(v.mid()._mpf_) for v in row] for row in jc]))
    A=[[arb(mp.nstr(inverse[i,j],180)) for j in range(3)] for i in range(3)]
    corrections=[abs(sum((A[i][j]*fc[j] for j in range(3)),arb(0))) for i in range(3)]
    rowsums=[]
    for i in range(3):
        rowsums.append(sum((abs(arb(int(i==j))-sum((A[i][k]*jb[k][j] for k in range(3)),arb(0)))
                              for j in range(3)),arb(0)))
    # The entrywise sum bounds every row sum; interval max comparisons
    # are avoided because overlapping balls are only partially ordered.
    q=sum(rowsums,arb(0));correction=sum(corrections,arb(0))
    assert q<1 and correction+q*radius<radius
    assert q<arb('2.79e-138') and correction<arb('4.15e-181')
    assert all(v.contains(0) for v in fb)
    word=(1,1,-1,-1);L=acb(0,box[2]);z=acb(box[0],box[1])
    zz,dd,rho,S1,action=orbit_arb(z,L,word)
    assert abs(S1)>1 and dd[-1].contains(1)
    assert rho.real<arb('-.019') and rho.real>arb('-.021')
    assert rho.imag.contains(0)
    for i in range(4):
        for j in range(i+1,4):assert abs(zz[i]-zz[j])>arb('.1')
    assert abs(zz[-1]-zz[0])<arb('1e-130')
    assert abs(action+4*box[2].log())<arb('1e-130')
    rotated=[]
    for j in range(4):
        ww=word[j:]+word[:j]
        _,_,rhor,_,_=orbit_arb(zz[j],L,ww)
        assert (rhor-rho).contains(0)
        rotated.append({'cyclic_shift':j,'residue':rhor.str(70)})
    zmp=mp.mpc(root[0],root[1]);Lmp=1j*root[2]
    def ret(z):
        for sign in word:z=mp.exp(sign*Lmp*z)
        return z
    a=mp.diff(ret,zmp,2)/2;b=mp.diff(ret,zmp,3)/6
    jet_rho=1-b/(a*a)
    assert abs(mp.diff(ret,zmp)-1)<mp.mpf('1e-195')
    assert abs(ret(zmp)-zmp)<mp.mpf('1e-195')
    assert abs(mp.im(jet_rho))<mp.mpf('1e-195')
    assert rho.contains(acb(mp.nstr(mp.re(jet_rho),170),mp.nstr(mp.im(jet_rho),170)))
    d=mp.findroot(lambda v:mp.cos(v)-v,mp.mpf('.74'));sd=mp.sin(d)
    alpha=sd+1j*d;Ld=1j*mp.exp(-sd);P=mp.exp(alpha);Q=mp.exp(1/alpha)
    def alternating(z):
        for sign in [1,-1,1,-1]:z=mp.exp(sign*Ld*z)
        return z
    aa=mp.diff(alternating,Q,2)/2;bb=mp.diff(alternating,Q,3)/6
    alt_rho=1-bb/(aa*aa)
    assert abs(alt_rho-sd/(6*(1+sd)))<mp.mpf('1e-195')
    return {'word_forward':list(word),'parameter_L':'i*y',
      'root_decimal_centers_180_digits':strings,'root_box_radius':'1e-140',
      'contraction_infinity_norm':q.str(50),'center_Newton_correction':correction.str(50),
      'independent_220dps_jacobian_error':mp.nstr(max(jac_errors),35),
      'strict_inclusion_lhs':(correction+q*radius).str(50),
      'stage_phases':[v.str(100) for v in zz[:4]],
      'multiplier':dd[-1].str(80),'nonzero_quadratic_factor_S1':S1.str(75),
      'iterative_residue':rho.str(100),'independent_220dps_jet_residue':mp.nstr(jet_rho,150),
      'lifted_action':action.str(100),'cyclic_rotation_checks':rotated,
      'alternating_equal_count_history':{'word_forward':[1,-1,1,-1],
         'parameter':'Dottie L*=i exp(-sin d)',
         'iterative_residue':mp.nstr(alt_rho,110),
         'exact_residue':'sin(d)/(6(1+sin(d)))'}}

def critical_constant():
    logarithm=2*arb(2).log()-4*arb.const_catalan()/arb.pi()
    value=logarithm.exp()
    partial=arb(0);bn=arb(1);N=4096
    for n in range(1,N+1):
        bn*=arb(2*n-1)/(2*n)
        partial+=bn*bn/(2*n)
    tail=arb(1)/(6*N)
    assert logarithm>partial and logarithm<partial+tail
    integral=(8/mp.pi)*mp.quad(lambda t:mp.log(mp.sin(t)),[mp.pi/4,mp.pi/2])
    assert abs(integral-(-2*mp.log(2)+4*mp.catalan/mp.pi))<mp.mpf('1e-210')
    return {'exact_critical_zeta':'4 exp(-4 Catalan/pi)',
      'directed_critical_value':value.str(100),
      'partial_log_series_terms':N,'partial_log_series':partial.str(80),
      'directed_log_tail_bound':tail.str(50),
      'independent_220dps_log_sine_integral':mp.nstr(integral,120)}

def main():
    start=time.perf_counter()
    out={'status':'primitive counts, Euler products, critical constant and certified signed fold all passed',
      'precision':{'arb_bits':ctx.prec,'independent_decimal_digits':mp.mp.dps},
      'counts':counts(),'four_stage_fold':certify_fold(),
      'critical_balanced_pair_zeta':critical_constant(),
      'elapsed_seconds':time.perf_counter()-start}
    (HERE/'signed-histories-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(out['status']);print('seconds',out['elapsed_seconds'])
    print('y',out['four_stage_fold']['root_decimal_centers_180_digits'][2])
    print('rho',out['four_stage_fold']['iterative_residue'])

if __name__=='__main__':main()
