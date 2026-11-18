"""Exhaustive exact lattice-ball certificate for bounded rational approximations.

Only SymPy's exact integer LLL is a dependency. All constants, enumeration bounds,
and final error comparisons use Python Fraction arithmetic, including certified
Machin-series bounds for pi and factorial-series bounds for e.
"""
from fractions import Fraction as F
from math import factorial, gcd, isqrt, ceil
from functools import reduce
from pathlib import Path
import json, time
from sympy import Matrix

HERE = Path(__file__).resolve().parent
H = 936
M = 10**19
E_CAP = F(263, 10**22)  # strict upper bound on original absolute error
D_CAP = 10400
K = ceil(M * E_CAP * D_CAP + 3*H)
R2 = 6*H*H + K*K
ORIGINAL = (-659, -183, 465, -936, 396, 155)

def add(a,b): return a[0]+b[0], a[1]+b[1]
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    p=[a[i]*b[j] for i in range(2) for j in range(2)]
    return min(p),max(p)
def div(a,b):
    assert not b[0] <= 0 <= b[1]
    return mul(a,(1/b[1],1/b[0]))
def scalar(v): return F(v),F(v)
def absolute(a):
    if a[0]>=0: return a
    if a[1]<=0: return neg(a)
    return F(0),max(-a[0],a[1])
def atan_inv(q,n=100):
    s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)), F(0))
    nextterm=F((-1)**n,(2*n+1)*q**(2*n+1))
    return min(s,s+nextterm),max(s,s+nextterm)

e_lo=sum((F(1,factorial(k)) for k in range(101)),F(0))
e=(e_lo,e_lo+F(1,100*factorial(100)))
pi=sub(mul(scalar(16),atan_inv(5)),mul(scalar(4),atan_inv(239)))
e2=mul(e,e)
T=div(mul(add(scalar(1),pi),add(scalar(2),pi)),sub(add(mul(pi,pi),pi),scalar(1)))
X=[scalar(1),e,e2,neg(T),neg(mul(T,e)),neg(mul(T,e2))]

def polynomial(c):
    return add(add(scalar(c[0]),mul(scalar(c[1]),e)),mul(scalar(c[2]),e2))
def error(c):
    return absolute(sub(div(polynomial(c[:3]),polynomial(c[3:])),T))
def decimal(x,digits=50,rounding=None):
    from decimal import Decimal,localcontext
    with localcontext() as ctx:
        ctx.prec=digits
        if rounding is not None: ctx.rounding=rounding
        return str(Decimal(x.numerator)/Decimal(x.denominator))
def export_interval(er,digits=65):
    from decimal import ROUND_FLOOR,ROUND_CEILING
    return [decimal(er[0],digits,ROUND_FLOOR),decimal(er[1],digits,ROUND_CEILING)]
def canonical(c):
    c=tuple(c)
    g=reduce(gcd,c)
    if not g: return c
    c=tuple(v//g for v in c)
    if next(v for v in c if v)!=abs(next(v for v in c if v)):
        c=tuple(-v for v in c)
    return c

def certify(height=936,candidate=ORIGINAL,error_cap=E_CAP,scale=10**19,out_path=None):
    """Prove global optimality inside the coefficient box using a known candidate.

    error_cap must be a rational strictly larger than the candidate's error.
    scale is the integer embedding scale; tune near 1/error_cap for efficiency.
    Returns JSON-serializable evidence and writes it only if out_path is given.
    """
    start=time.time()
    H=int(height); M=int(scale); E_CAP=F(error_cap)
    D_CAP=ceil(H*(1+e[1]+e2[1]))
    K=ceil(M*E_CAP*D_CAP+3*H)
    R2=6*H*H+K*K
    assert max(map(abs,candidate))<=H
    assert H*(1+e[1]+e2[1])<D_CAP
    original_error=error(ORIGINAL)
    candidate_error=error(candidate)
    assert candidate_error[1]<E_CAP
    q=[]
    for lo,hi in X:
        a=(M*lo+F(1,2)).numerator//(M*lo+F(1,2)).denominator
        b=(M*hi+F(1,2)).numerator//(M*hi+F(1,2)).denominator
        assert a==b
        assert scalar(-F(1,2))[0] < M*lo-a and M*hi-a < F(1,2)
        q.append(a)
    lattice=Matrix([[int(i==j) for j in range(6)]+[q[i]] for i in range(6)])
    Bm=lattice.lll(delta=F(3,4))
    B=[[int(v) for v in Bm.row(i)] for i in range(6)]
    # Identity columns prove LLL's row transformation is unimodular, and every
    # last coordinate still equals the exact q-dot-coefficient embedding.
    U=Matrix([r[:6] for r in B])
    assert abs(U.det())==1
    assert all(sum(row[i]*q[i] for i in range(6))==row[6] for row in B)
    bstar=[]; norms=[]; mu=[[F(0) for _ in range(6)] for _ in range(6)]
    for i,row in enumerate(B):
        v=[F(x) for x in row]
        for j in range(i):
            mu[i][j]=sum(F(row[k])*bstar[j][k] for k in range(7))/norms[j]
            v=[v[k]-mu[i][j]*bstar[j][k] for k in range(7)]
        bstar.append(v)
        norms.append(sum(x*x for x in v))
    counts={"recursive_nodes":0,"lattice_points_in_ball":0,"box_points":0,"primitive_sign_classes":0}
    z=[0]*6; candidates={}
    def visit(j,remaining):
        counts['recursive_nodes']+=1
        if j<0:
            counts['lattice_points_in_ball']+=1
            c=tuple(sum(z[i]*B[i][k] for i in range(6)) for k in range(6))
            if max(map(abs,c))>H or not any(c): return
            counts['box_points']+=1
            if reduce(gcd,c)!=1: return
            c=canonical(c)
            if c in candidates: return
            den=polynomial(c[3:])
            if den==(F(0),F(0)): return
            assert not den[0]<=0<=den[1], 'interval too wide'
            candidates[c]=error(c)
            return
        shift=sum(mu[k][j]*z[k] for k in range(j+1,6))
        rad2=remaining/norms[j]
        root=isqrt(rad2.numerator//rad2.denominator)
        if F(root*root)<rad2: root+=1
        center=-shift
        low=center.numerator//center.denominator-root-1
        high=center.numerator//center.denominator+root+2
        for v in range(low,high+1):
            used=norms[j]*(v+shift)**2
            if used<=remaining:
                z[j]=v
                visit(j-1,remaining-used)
        z[j]=0
    visit(5,F(R2))
    counts['primitive_sign_classes']=len(candidates)
    ranked=sorted(candidates.items(),key=lambda p:(p[1][0]+p[1][1])/2)
    winner,win_error=ranked[0]
    assert all(other[0]>win_error[1] for c,other in ranked[1:])
    if H==936: assert winner==canonical(ORIGINAL)
    # This proves winner beats every enumerated class, and the candidate's
    # cap proves any unenumerated box vector cannot improve the original.
    result={
        "theorem":f"Unique primitive coefficient sign class minimizing absolute ratio error under H={H}",
        "H":H,"M":M,"error_cap":str(E_CAP),"denominator_cap":D_CAP,
        "initial_candidate":list(candidate),"initial_candidate_error_interval":export_interval(candidate_error),
        "last_coordinate_cap":K,"squared_radius":R2,
        "q":q,"lll_basis":B,"basis_transform_determinant":int(U.det()),
        "counts":counts,"winner":winner,
        "winner_error_interval":export_interval(win_error),
        "original_error_interval":export_interval(original_error),
        "top_candidates":[{"coefficients":c,"height":max(map(abs,c)),"absolute_error_interval":export_interval(er)} for c,er in ranked[:20]],
        "all_enumerated_primitive_sign_classes":[{"coefficients":c,"height":max(map(abs,c)),"absolute_error_interval":export_interval(er),"strictly_improves_original":er[1]<original_error[0]} for c,er in ranked],
        "elapsed_seconds":time.time()-start,
        "verification":"All constant bounds, q rounding, Gram-Schmidt values, enumeration inequalities, and winning-error comparisons used exact Fraction arithmetic. pi via alternating Machin series, e via factorial series."
    }
    if out_path: Path(out_path).write_text(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('--height',type=int,default=936)
    p.add_argument('--candidate',type=int,nargs=6,default=ORIGINAL)
    p.add_argument('--error-cap',default=str(E_CAP))
    p.add_argument('--scale',type=int,default=10**19)
    p.add_argument('--output',default=str(HERE/'certificate.json'))
    args=p.parse_args()
    result=certify(args.height,tuple(args.candidate),F(args.error_cap),args.scale,args.output)
    print(json.dumps({k:v for k,v in result.items() if k not in ['all_enumerated_primitive_sign_classes','lll_basis','q']},indent=2),flush=True)
