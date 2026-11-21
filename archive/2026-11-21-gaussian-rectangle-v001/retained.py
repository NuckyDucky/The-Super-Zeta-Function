"""The six retained signed bands and the upper bound for every norm above X."""
import hashlib
import json
import math
import sys
from functools import lru_cache
from pathlib import Path

from flint import acb, arb, ctx, fmpz

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "2026-11-20-gaussian-endpoint-parity-v001"))
from gaussian_inputs import height, sign


@lru_cache(maxsize=100000)
def prime_signs(p):
    assert fmpz(p).is_prime()
    if p == 2:
        return (sign(1,1),)
    if p % 4 == 3:
        return (sign(p,0),)
    r = int(fmpz(p-1).sqrtmod(fmpz(p)))
    a,b = p,min(r,p-r)
    while b*b > p:
        a,b = b,a%b
    k = math.isqrt(p-b*b)
    assert b*b+k*k == p
    return (sign(b,k),sign(b,-k))


def coefficient(n):
    result, checked = 1,1
    for p,e in fmpz(n).factor():
        p,e = int(p),int(e)
        checked *= p**e
        chars = prime_signs(p)
        if p%4 == 3:
            result *= 0 if e%2 else chars[0]**(e//2)
        elif p == 2:
            result *= chars[0]**e
        else:
            a,b = chars
            result *= sum(a**k*b**(e-k) for k in range(e+1))
    assert checked == n
    return result


def verify_small(limit=4096):
    vals = [0]*(limit+1)
    for a in range(1,math.isqrt(limit)+1):
        for b in range(math.isqrt(limit-a*a)+1):
            vals[a*a+b*b] += sign(a,b)
    assert all(coefficient(n)==vals[n] for n in range(1,limit+1))


def smoothing(s,n,B,T):
    ell = (B/n).log()+s.log()-acb(0,arb.pi()/2)
    V0 = (-ell/2).erfc()/2
    first = (-(ell**2)/4).exp()/(2*arb.pi().sqrt())
    V = V0 + (-ell/2-1)*first/(2*s)
    assert T>arb("4e12") and abs(T-s.imag) < arb(1)/16
    assert s.real > arb("0.46") and s.real < arb("0.54")
    assert B*T/n < 5
    err = arb(4000)/(T*T)+arb("1e-100")
    enclosure = arb(0,err.upper())
    return V + acb(enclosure,enclosure)

def band_evaluator(d, phase):
    T, B = phase.arc.T, phase.arc.B
    h=d["anchor"]
    lh=arb(h).log()
    base = phase.arc.gamma0*(-phase.s0*lh).exp()
    slopes = phase.arc.logBt-lh
    L = max(abs((arb(d["lo"])/h).log()),abs((arb(d["hi"])/h).log())).upper()
    E = 4000/T**2+arb("1e-100")
    error = (d["mass"]*(4*L+4*E)).upper()
    carrier=acb(arb(d["carrier"][0]),arb(d["carrier"][1]))
    square=acb(arb(0,error),arb(0,error))
    def piece(z):
        s=phase.s0+z
        assert abs(s-acb(0,T)) < 1
        terr=3*abs(z)/(T-1)
        g=base*(z*slopes+acb(arb(0,terr.upper()),arb(0,terr.upper()))).exp()
        return g*(carrier*smoothing(s,h,B,T)+square)
    def evaluate(z):
        return piece(z)+piece(-z.conjugate()).conjugate()
    return evaluate


def far_tail_bound(T, B, padding):
    K, pi, k = T * B, arb.pi(), arb(8)
    ceiling = int((arb(17).exp() * K).ceil().unique_fmpz())
    X = arb(ceiling)
    eta=arb(35)/2048+padding
    sig=arb(1)/2-arb(63)/2048-padding
    assert sig>0 and sig<1
    ex=(pi*eta/2+k**2+k*eta/T+k*(k+1)*(2*k+1)/(12*T*T)
        +(k+arb(1)/2)**2/(4*T*T)+k*(K/X).log())
    bound = (24/(2*pi*k)*pi.sqrt()*X*(B/X)**sig*(1+2*pi*(T+eta)).sqrt()
            /(B**2*(2*pi*T*(1+T*T)).sqrt())*(k+sig)/(k+sig-1)*ex.exp())
    return ceiling, bound.upper()

if __name__ == "__main__":
    if not __debug__:
        sys.exit("Run with assertions enabled.")
    # Match the Dottie height enclosure shared by the published circle replays.
    ctx.prec = 192
    T = height()
    ctx.prec = 256
    verify_small()
    for row in json.loads((HERE / "carriers.json").read_text()):
        lo, hi, h = row["lo"], row["hi"], row["anchor"]
        digest = hashlib.sha256()
        total, mass = acb(0), 0
        for n in range(lo, hi + 1):
            a = coefficient(n)
            digest.update((("" if n == lo else ",") + str(a)).encode())
            if a:
                total += a * acb(0, -T * (arb(n-h) / h).log1p()).exp()
                mass += abs(a)
        assert digest.hexdigest() == row["sha256"] and mass == row["mass"]
        # Both computations use the same interval formula on the same exact coefficients.
        assert [str(total.real), str(total.imag)] == row["carrier"]
        print("Verified signed band", lo, hi, flush=True)
