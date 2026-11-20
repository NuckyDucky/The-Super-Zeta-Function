"""Independent interval check at the second period-640 stationary point.

This implementation follows the original antiholomorphic half-step in real
coordinates. The interval evaluator and its real jets were extracted from
computations/certify_finite_stationarity.py of the finite-stationarity study.
Input Newton centers only precondition the directed inclusion test.
"""
from fractions import Fraction
from pathlib import Path
import json
import mpmath as mp
from flint import acb, arb, ctx, fmpq

def rational_ball(text, radius=None):
    f = Fraction(text)
    return arb(fmpq(f.numerator, f.denominator), radius)


def exact_mp_ball(value):
    sign, mantissa, exponent, _ = value._mpf_
    return arb(((-1 if sign else 1) * mantissa, exponent))


def proper_tests(n):
    factors, d, remaining = [], 2, n
    while d*d <= remaining:
        if remaining % d == 0:
            factors.append(d)
            while remaining % d == 0:
                remaining //= d
        d += 1
    if remaining > 1:
        factors.append(remaining)
    return [n // d for d in factors]


class J1:
    """First real jet; derivatives are with respect to x,t,y."""
    def __init__(self, value, gradient=None):
        self.v = value if isinstance(value, arb) else arb(value)
        self.g = gradient if gradient is not None else [arb(0) for _ in range(3)]

    def __add__(self, other):
        if not isinstance(other, J1):
            other = J1(other)
        return J1(self.v + other.v, [a+b for a,b in zip(self.g,other.g)])

    __radd__ = __add__

    def __neg__(self):
        return J1(-self.v, [-a for a in self.g])

    def __sub__(self, other):
        return self + (-other if isinstance(other,J1) else -J1(other))

    def __rsub__(self, other):
        return J1(other)-self

    def __mul__(self, other):
        if not isinstance(other,J1):
            other=J1(other)
        return J1(self.v*other.v,[a*other.v+self.v*b for a,b in zip(self.g,other.g)])

    __rmul__=__mul__


def system(centers, radii, p):
    x,t,y=[rational_ball(c,r) for c,r in zip(centers,radii)]
    z0=z=acb(x,t)
    i=acb(0,1)
    first=[acb(1),i,acb(0)]
    second=[[acb(0) for _ in range(3)] for _ in range(3)]
    S=J1(0);w=J1(0);v=[J1(0),J1(0)]
    gaps={}
    tests=proper_tests(p)
    for k in range(p):
        S=S+J1(z.imag,[j.imag for j in first])
        w=w+J1(first[2].imag,[second[2][j].imag for j in range(3)])
        for alpha in range(2):
            v[alpha]=v[alpha]+J1(first[alpha].imag,[second[alpha][j].imag for j in range(3)])
        exponent=i*y*z.conjugate()
        wi=[i*(y*first[j].conjugate()+(z.conjugate() if j==2 else 0)) for j in range(3)]
        wij=[[i*(y*second[a][b].conjugate()
                  +(first[b].conjugate() if a==2 else 0)
                  +(first[a].conjugate() if b==2 else 0))
              for b in range(3)] for a in range(3)]
        zn=exponent.exp()
        second=[[zn*(wij[a][b]+wi[a]*wi[b]) for b in range(3)] for a in range(3)]
        first=[zn*j for j in wi]
        z=zn
        if k+1 in tests:
            gaps[k+1]=abs(z-z0)
        if not z.is_finite():
            raise ArithmeticError(f"interval orbit lost finiteness at step {k+1}")
    A=[[J1(first[c].real,[second[c][j].real for j in range(3)]) for c in range(2)],
       [J1(first[c].imag,[second[c][j].imag for j in range(3)]) for c in range(2)]]
    b=[J1(first[2].real,[second[2][j].real for j in range(3)]),
       J1(first[2].imag,[second[2][j].imag for j in range(3)])]
    D=[[1-A[0][0],-A[0][1]],[-A[1][0],1-A[1][1]]]
    delta=D[0][0]*D[1][1]-D[0][1]*D[1][0]
    adjb=[D[1][1]*b[0]-D[0][1]*b[1],-D[1][0]*b[0]+D[0][0]*b[1]]
    yy=J1(y,[arb(0),arb(0),arb(1)])
    N=delta*(p+yy*S+yy*yy*w)+yy*yy*(v[0]*adjb[0]+v[1]*adjb[1])
    F=[J1(z.real-x,[first[j].real-(1 if j==0 else 0) for j in range(3)]),
       J1(z.imag-t,[first[j].imag-(1 if j==1 else 0) for j in range(3)]),N]
    return [f.v for f in F],[f.g for f in F],delta.v,gaps


def main():
    mp.mp.dps = 190
    ctx.dps = 230
    p = 640
    radius = "1e-130"
    path = Path(__file__).with_name("secondary-center.json")
    centers = json.loads(path.read_text(encoding="utf-8"))
    pointF,pointJ,_,_=system(centers,[None]*3,p)
    midpointJ=mp.matrix([[mp.mpf(a.mid()._mpf_) for a in row] for row in pointJ])
    inverse=midpointJ**-1
    C=[[exact_mp_ball(inverse[i,j]) for j in range(3)] for i in range(3)]
    F,J,delta,gaps=system(centers,[radius]*3,p)
    B=[[arb(int(i==j))-sum(C[i][k]*J[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    correction=[-sum(C[i][k]*pointF[k] for k in range(3)) for i in range(3)]
    error=[correction[i]+sum(B[i][j]*arb(0,radius) for j in range(3)) for i in range(3)]
    ratios=[abs(e).upper()/arb(radius) for e in error]
    inclusion=all(r<1 for r in ratios)
    contraction=max(sum(abs(a).upper() for a in row) for row in B)
    primitive=all(g.abs_lower()>0 for g in gaps.values())
    # Closure Jacobian rows are A-I and b. Recover the branch tangent
    # from exactly the interval jets used in the Krawczyk calculation.
    D11,D12,D21,D22=-J[0][0],-J[0][1],-J[1][0],-J[1][1]
    bx,bt=J[0][2],J[1][2]
    tx=(D22*bx-D12*bt)/delta
    tt=(-D21*bx+D11*bt)/delta
    yy=rational_ball(centers[2],radius)
    curvature=(J[2][0]*tx+J[2][1]*tt+J[2][2])/(yy*delta)
    coefficient_abs=abs(acb(J[0][0]+1,J[1][0]))
    cap_distance = abs(acb(rational_ball(centers[0], radius)-1, rational_ball(centers[1], radius)))
    # Certify that this independent root belongs to the same marked disk and
    # the same parameter bracket as the alternating-stage certificate.
    bracket_center = rational_ball("0.5098930237333223092469862115108741354")
    in_bracket = abs(yy-bracket_center) < rational_ball("1e-24")
    if not (inclusion and contraction < 1 and primitive and abs(delta)>0
            and curvature>0 and coefficient_abs<1 and cap_distance<rational_ball("1e-6")
            and in_bracket):
        raise ArithmeticError("the independent checks did not all pass")
    print(json.dumps({
        "p": p, "working_decimal_digits": ctx.dps, "box_halfwidth": radius,
        "strict_krawczyk_inclusion": inclusion,
        "krawczyk_radius_ratios": [a.str(16) for a in ratios],
        "derivative_defect_infinity": contraction.str(16),
        "log_modulus_curvature": curvature.str(20),
        "return_modulus": coefficient_abs.str(20),
        "inside_cap_disk_and_parameter_bracket": True,
        "proper_divisor_distance_lower": {str(k):g.abs_lower().str(16) for k,g in gaps.items()}
    }, indent=2))


if __name__ == "__main__":
    main()
