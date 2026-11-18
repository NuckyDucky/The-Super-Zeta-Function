"""Integer values of the unshifted reciprocal superzeta (coupling one).

Proof. Write S_n=Z(n;1), B_n=F(n) for its reference cosine spectrum, and
E(x)=cos(sqrt(x))**2-x. Then sum S_n x**n = -x E'(x)/E(x). The coefficient
of x**n is rational. Dropping -x from E gives the analogous reference sum.

Put y=2x, z=sqrt(2y), C=cos(z), U=sin(z)/z and V=sin(2z)/(2z). All three
are formal series in y. Use exponential generating series over the 2-adic
integers: write T_n=n![y^n]T; products use integer binomial coefficients,
and a series with odd constant has a reciprocal in the same ring.
We have c_n=(-1)^n/(2n-1)!!, u_n=c_n/(2n+1), v_n=4**n*u_n.
With P(y)=sum S_n*(y/2)^n, logarithmic differentiation gives
P=y*(1+U)/(1+C-y). Multiplying by 1-C-y and using C*U=V and
C**2+2*y*U**2=1 gives

    P = ((1-C+U-V)/y -(1+U)) / (1+2*(U**2-1)/y).

Set W=(U**2-1)/y. From U**2=(1-cos(2z))/(4y),
v2(W_n)=2*(n+1)-v2(n+1)-v2(n+2) >= 1 for all n>=0.
Here consecutive numbers have only one even member and n+2<=2**(n+1).
Thus the displayed denominator is 1 modulo 4 in the exponential-series
ring. For A=(1-C+U-V)/y, its normalized nth coefficient is
    A_n=-2*c_(n+1)/(2n+3) - 4**(n+1)*u_(n+1)/(n+1).
The first term equals 2 mod 4, and the second is 0 mod 4. Consequently,
for all n>=1, P_n=2-u_n=u_n=(-1)**floor(n/2) mod 4. The last equality
uses u_n=(-1)^n/(2n+1)!! and counts the factors congruent to 3 mod 4.
Since P_n=n! S_n/2**n is odd, v2(S_n)=n-v2(n!)=popcount(n).
Furthermore (2n)! S_n/4**n=(2n-1)!! P_n is 1 mod 4 and an integer:
in the variable t=sqrt(x), E(t**2) has integer exponential coefficients
and constant 1; so does its reciprocal, and -(t/2)dE(t**2)/dt has
integer exponential coefficients (each even index 2n contributes -n).
This proves (2n)! S_n is an integer; the valuation just proved cancels 4**n.

Reference comparison by the same algebra: P0(y)=sum B_n*(y/2)^n
=y*U/(1+C). Then 2*P0=(1-C)/U. Modulo 2, the exponential coefficients
of C and U are all 1. The exponential series H with these coefficients
satisfies H**2=1 mod 2 (positive coefficients 2**n). Hence 2*P0=1+H
mod 2: every normalized positive coefficient is odd. Therefore
v2(B_n)=popcount(n)-1, and v2(S_n-B_n)=v2(B_n).

Replay: python -B superzeta_binary_traces.py
The 128-term rational calculation uses the standard library. The 65,536-term
modular calculation uses python-flint 0.9.0, with an exact modulus of 2**32.
"""
from fractions import Fraction
from math import factorial


def rational_values(nmax, coupled):
    e = [Fraction(1)]
    traces = [Fraction(0)]
    for n in range(1, nmax + 1):
        coef = Fraction((-1)**n * 2**(2*n-1), factorial(2*n))
        e.append(coef - int(coupled and n == 1))
        traces.append(-n*e[n] - sum(e[j]*traces[n-j] for j in range(1, n)))
    return traces


def v2(n):
    if n == 0:
        raise ValueError("The valuation of zero is infinite")
    return (n & -n).bit_length()-1


def exact_check():
    traces = rational_values(128, True)
    reference = rational_values(128, False)
    for n in range(1, 129):
        normalized = factorial(2*n)*traces[n]/4**n
        assert normalized.denominator == 1 and normalized.numerator % 4 == 1
        for q, expected in ((traces[n], n.bit_count()), (reference[n], n.bit_count()-1),
                            (traces[n]-reference[n], n.bit_count()-1)):
            assert v2(q.numerator)-v2(q.denominator) == expected
    print("Exact rational checks, n=1..128. First four normalized integers:",
          [int(factorial(2*n)*traces[n]/4**n) for n in range(1,5)])
    # If p is odd, e_j is p-integral up to j<m=(p+1)/2. At j=m
    # the (p+1)! denominator has one factor p and p does not divide m.
    # Hence the logarithmic-derivative recurrence gives v_p(S_m)=-1.
    for p in range(3, 256, 2):
        if any(p % d == 0 for d in range(3, int(p**0.5)+1, 2)):
            continue
        m = (p+1)//2
        assert all(trace.denominator % p for trace in traces[1:m])
        assert traces[m].denominator % p == 0 and traces[m].denominator % (p*p) != 0
    print("First denominator occurrence verified for odd primes up to 251.")


def modular_check(nmax=65536):
    from flint import nmod_poly
    modulus = 2**32
    coefficients = [1]
    factorial_odd_parts = [1]
    for n in range(1, nmax+1):
        # Odd part of (2n)! from that of (2n-2)!; no division by even residues.
        odd = factorial_odd_parts[-1] * (2*n-1) * (n >> v2(n)) % modulus
        factorial_odd_parts.append(odd)
        coefficients.append((-1)**n * (1 << (n.bit_count()-1)) * pow(odd, -1, modulus) % modulus)
    for coupled in (False, True):
        e = coefficients.copy()
        e[1] -= int(coupled)
        f = nmod_poly(e, modulus)
        num = nmod_poly([-n*c % modulus for n,c in enumerate(e)], modulus)
        trace = num.mul_low(f.inverse_series_trunc(nmax+1), nmax+1)
        for n in range(1, nmax+1):
            value = int(trace[n])
            assert v2(value) == n.bit_count()-int(not coupled)
            if coupled:
                assert (value >> n.bit_count()) * factorial_odd_parts[n] % 4 == 1
    print(f"Both spectra verified modulo 2^32 through n={nmax}.")


if __name__ == "__main__":
    exact_check()
    modular_check()
