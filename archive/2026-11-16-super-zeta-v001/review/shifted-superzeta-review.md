# Independent mathematical review of the shifted superzeta

16 November 2026. Reviewed `research/shifted-superzeta.md` against the
established cosine determinant and independently derived its residue,
Mellin, gamma–Bessel, determinant and tail formulas. The root agent is
separately implementing and replaying its directed numerical verifier.

**Outcome:** the formulas and their stated real-shift/right-half-plane
coupling domains are correct.

## Cut and Mellin domain

For \(v\ge0\), a zero of
\(E_\varepsilon(-v)=\cosh^2\sqrt v+v/\varepsilon^2\) would force
\(\varepsilon^2=-v\operatorname{sech}^2\sqrt v\). This is impossible
when \(\Re\varepsilon>0\). The same argument shows that the principal
logarithm in \(F_\varepsilon\) has no cut crossing in that half-plane.
Adding a real nonnegative shift preserves the principal spectral cut.

The genus-zero canonical product gives the logarithmic derivative as the
sum of shifted resolvents. The beta integral is valid for each off-cut
eigenvalue. The established square-root zero count makes the sum absolute
for \(\Re s>1/2\); the integral endpoint requires \(\Re s<1\).
Thus the exact defining Mellin strip is the printed
\(1/2<\Re s<1\).

## Every central-binomial residue

At infinity the entire power expansion of the logarithmic derivative is
\[
(t+w)^{-1/2}
=\sum_{n\ge0}(-1)^nB_nw^nt^{-n-1/2}.
\]
Each Mellin term has residue \((-1)^nB_nw^n\) before multiplication by
the sine. At \(s=1/2-n\), that sine contributes \((-1)^n/\pi\).
Hence the exact residue is \(B_nw^n/\pi\), including its sign and
normalization. For \(w\ne0\), each one is nonzero. Analyticity at the
small endpoint gives positive-integer Mellin poles canceled by the sine;
nonpositive integers have a regular integral and therefore zero spectral
value.

At zero, the finite part of the integrated logarithmic derivative is
\(-\log4-\log E_\varepsilon(-w)\), since
\(\log E_\varepsilon(-w-T)=2\sqrt{T+w}-\log4+o(1)\).
This verifies the determinant **\(4E_\varepsilon(-w)\)** and its sign.

## Gamma–Bessel representation and its tail

The reference spectrum has multiplicity two at
\(\pi^2(n+1/2)^2\). Its heat trace is
\[
\frac1{\sqrt{\pi t}}\sum_{m\in\mathbb Z}(-1)^me^{-m^2/t}.
\]
Mellin integration gives the printed gamma quotient and the coefficient
\(4/(\sqrt\pi\Gamma(s))\) in the Bessel series. Its gamma-quotient
residue is independently
\[
\frac{(-1)^n}{n!\sqrt\pi\Gamma(1/2-n)}w^n
=\frac{B_nw^n}{\pi}.
\]
The relative correction integral is entire after its positive-integer
endpoint cancellations, and its derivative at zero is
\(-F_\varepsilon(w)\), as required by the determinant.

For complex order, \(|\cosh((a+ib)t)|\le\cosh(at)\). Using
\(\cosh t\ge1+t^2/2\) in the standard integral for \(K\) gives even
a factor-two sharper Gaussian bound than the one printed. The printed
larger bound is valid. Its power/exponential ratio estimate gives exactly
the denominator condition in (11), with no missing winding multiplicity.

## Single integral and resolvent differentiation

Direct algebra gives
\[
Q'(v)-Q(v)/\sqrt v
=\varepsilon^{-2}(1-\sqrt v)
-\frac{1+e^{-2\sqrt v}}{2\sqrt v},
\]
which proves the numerator in \(H_\varepsilon\). Its exponential
large-argument decay gives the stated continuation formula. For real
positive coupling and \(t=x^2\), use
\(\sqrt{w+x^2}\le x+w\) when \(x\ge1\),
\(Q\ge e^{2x}/4\), and \(1/\sqrt{w+x^2}\le1/\sqrt w\).
The factor from \(dt=2x\,dx\) is eight, exactly as printed.
For each remaining power \(x^a\), the geometric-exponential majorant
gives \(U_a(T)\) and its denominator condition. Integration at zero
then yields \(2\sqrt w-\log(4Q(w))\).

Finally, differentiation in the absolutely convergent spectral half-plane
proves the Pochhammer shift identity. Its continuation and the logarithmic
determinant give every positive-integer resolvent trace with the stated
factor \((-1)^{m-1}/(m-1)!\). The coupling-stationary numerator is
\(1-\sqrt v\tanh\sqrt v\), correctly recovering the Laplace equation.

The note preserves the distinct meanings of the residue index and quartet
radius index when matching them in the normalization observable.
