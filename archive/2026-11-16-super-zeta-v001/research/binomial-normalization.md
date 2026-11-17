# Balanced sign counts, the quartet spectrum, and an exact Barnes constant

16 November 2026. This continues NuckyDucky's observation that the balanced-sign
probability cancels the leading quartet radius. It retains the lower-order
terms through the entire product and gives a controlled finite-cutoff formula.

Let
\[
B_n=4^{-n}\binom{2n}{n},\qquad
C_n=\frac{R_nB_n^2}{2},\qquad
D_n=\pi nB_n^2.
\]
Here \(R_n\) is the common radius of the \(n\)-th nonunit parabolic
quartet. The existing exact radial product is
\[
\prod_{n\ge1}\frac{R_n}{2\pi n}=e^{\sin d/2},\qquad d=\cos d.
\tag{1}
\]
All logarithms below are real logarithms of positive quantities.

## 1. The exact global normalization

**Theorem.** Define the normalized finite product
\[
S_N=N^{1/4}\prod_{n=1}^N C_n.
\]
Then
\[
\boxed{\lim_{N\to\infty}S_N
=K:=\frac{e^{\sin d/2}}{G(3/2)^2},}
\tag{2}
\]
where \(G\) is the Barnes \(G\)-function normalized by
\(G(1)=1\), \(G(z+1)=\Gamma(z)G(z)\). Numerically,
\[
\boxed{K=1.2250017073142016852999108811594267460129879373138051\ldots.}
\tag{3}
\]
The exact finite identity behind this limit is
\[
\boxed{
\prod_{n=1}^N C_n
=\left(\prod_{n=1}^N\frac{R_n}{2\pi n}\right)
\frac{\Gamma(N+1)}{G(3/2)^2}
\left[\frac{G(N+3/2)}{G(N+2)}\right]^2.}
\tag{4}
\]

**Proof.** The duplication formula gives
\[
B_n=\frac{\Gamma(n+1/2)}{\sqrt\pi\,\Gamma(n+1)},
\quad
D_n=n\frac{\Gamma(n+1/2)^2}{\Gamma(n+1)^2},
\quad C_n=\frac{R_n}{2\pi n}D_n.
\]
Iterating the Barnes recurrence gives exactly
\[
\prod_{n=1}^N D_n
=\Gamma(N+1)
\left[\frac{G(N+3/2)}{G(3/2)G(N+2)}\right]^2,
\]
which proves (4). The standard Barnes and Stirling expansions imply
\[
\log\Gamma(N+1)+2\log G(N+3/2)-2\log G(N+2)
=-\tfrac14\log N+O(N^{-1}).
\tag{5}
\]
For clarity, in \(F(x)=\log G(x+1)\), the first two shifted differences
are \(-F'(N)-3F''(N)/4+O(N^{-1})\). Their respective leading terms cancel
the \(N\log N\), \(N\), \(\log(2\pi)\) and all but
\(-\log N/4\) from \(\log\Gamma(N+1)\). The constant term is zero.
Combining (5) with (1) proves (2). ∎

The published inputs are the gamma/Stirling formulas in
[NIST DLMF §5.11](https://dlmf.nist.gov/5.11) and the Barnes recurrence and
asymptotic expansion in [§5.17](https://dlmf.nist.gov/5.17). The factor
\(e^{\sin d/2}\) is the exact input from the reciprocal quartet spectrum.

The first finite-level terms make the exponent \(1/4\) explicit. With
\(L_n=\log(2\pi n)\),
\[
\boxed{C_n=1-\frac1{4n}
+\frac{\frac1{32}+\frac{2L_n^2-2L_n-1}{4\pi^2}}{n^2}
+O((\log n)^2/n^3).}
\tag{6}
\]
Thus \(n(1-C_n)\to1/4\), and the effective linear levels
\(\Lambda_n=nC_n\) satisfy \(\Lambda_n=n-1/4+o(1)\).
The pointwise cancellation \(C_n\to1\), the accumulated factor
\(N^{-1/4}\), and the limiting constant (2) are successive terms of the
same normalization calculation.

## 2. An exact positive-kernel formula controls every Stirling truncation

**Lemma.** For every real \(x>0\),
\[
\boxed{\log\left[x\frac{\Gamma(x+1/2)^2}{\Gamma(x+1)^2}\right]
=-\int_0^\infty e^{-xt}\frac{\tanh(t/4)}t\,dt.}
\tag{7}
\]
Consequently, putting
\[
d_{2m-1}=-\frac{4(1-2^{-2m})B_{2m}}{(2m)(2m-1)},
\tag{8}
\]
one has for every integer \(M\ge1\)
\[
\boxed{\left|\log D_n-\sum_{m=1}^M
\frac{d_{2m-1}}{n^{2m-1}}\right|
\le\frac{|d_{2M+1}|}{n^{2M+1}}.}
\tag{9}
\]
The remainder has the sign of the next coefficient.

**Proof.** The digamma integral
[DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16) gives
\[
\psi(x+1)-\psi(x+1/2)
=\int_0^\infty\frac{e^{-xt}}{e^{t/2}+1}\,dt.
\]
Differentiating the left side of (7) therefore gives
\(\int_0^\infty e^{-xt}\tanh(t/4)\,dt\). Its value tends to zero as
\(x\to\infty\) by Stirling's formula, proving (7) by integration.

Logarithmic differentiation of the hyperbolic-cosine product gives
\[
\frac{\tanh(t/4)}t
=8\sum_{j=0}^\infty
\frac1{4\pi^2(2j+1)^2+t^2}.
\tag{10}
\]
The product is [DLMF 4.36.2](https://dlmf.nist.gov/4.36.E2). In each
positive denominator, the finite geometric expansion in \(t^2\) has an
alternating remainder bounded by its next monomial. Integrating against
\(e^{-nt}\), and summing the positive coefficient bounds, gives (9).
The coefficients are precisely (8), also obtained by subtracting the two
ordinary Stirling series. ∎

In particular
\[
\log D_n=-\frac1{4n}+\frac1{96n^3}-\frac1{320n^5}
+\frac{17}{7168n^7}-\frac{31}{9216n^9}+\cdots.
\tag{11}
\]
The controlled tail here follows from the positive-kernel proof, with an
explicit bound for every positive integer \(n\).

## 3. The full finite-cutoff correction

Write
\[
T_D(N)=\log\Gamma(N+1)+2\log G(N+3/2)-2\log G(N+2)
+\tfrac14\log N,
\]
\[
T_R(N)=\sum_{n>N}\log\frac{R_n}{2\pi n}.
\]
Equation (4) and the exact radial product imply the exact identity
\[
\boxed{\log S_N=\log K+T_D(N)-T_R(N).}
\tag{12}
\]
Both correction terms now have explicit controlled approximations.

For the Barnes/Stirling term, let \(\zeta(q,a)\) denote the Hurwitz zeta
and let \(\psi\) denote the digamma function. For \(M\ge1\), put
\[
\widetilde T_{D,M}(N)
=-\frac14[\psi(N+1)-\log N]
-\sum_{m=2}^M d_{2m-1}\zeta(2m-1,N+1).
\tag{13}
\]
Then (9), summed over \(n>N\), proves
\[
\boxed{|T_D(N)-\widetilde T_{D,M}(N)|
\le |d_{2M+1}|\zeta(2M+1,N+1).}
\tag{14}
\]
To derive (13), subtract \(-1/(4n)\) from (11), use
\(H_N-\log N-\gamma=\psi(N+1)-\log N\), and use the limiting
constant already proved in (5).

The radial term uses the earlier controlled quartet expansion
\[
\log\frac{R_n}{2\pi n}
=\sum_{j\ge1}\chi_j(\log(2\pi n))(2\pi n)^{-2j},
\]
with
\[
\chi_1(L)=2L^2-2L-1,
\quad
\chi_2(L)=-4L^4+\tfrac{64}3L^3-16L^2-6L+\tfrac12.
\]
Let
\[
H_N(q)=(2\pi)^{-q}\zeta(q,N+1),
\quad
\widetilde T_{R,J}(N)=\sum_{j=1}^J
\chi_j(-\partial_q)H_N(q)\big|_{q=2j}.
\tag{15}
\]
The prior explicit Cauchy disk gives, for
\(\eta_N=256(1+\log(2\pi N))^2/(2\pi N)^2<1\),
\[
\boxed{|T_R(N)-\widetilde T_{R,J}(N)|\le E_{R,J}(N),}
\]
\[
E_{R,J}(N)=\frac{256^{J+1}}{8(1-\eta_N)}
\int_N^\infty
\frac{(1+\log(2\pi x))^{2J+2}}{(2\pi x)^{2J+2}}\,dx.
\tag{16}
\]
The integral is an elementary finite sum after \(x=Ne^u\). Thus the
corrected finite estimator
\[
\widehat k_{N,M,J}
=\log S_N-\widetilde T_{D,M}(N)+\widetilde T_{R,J}(N)
\]
has the rigorous error
\[
\boxed{|\widehat k_{N,M,J}-\log K|
\le |d_{2M+1}|\zeta(2M+1,N+1)+E_{R,J}(N).}
\tag{17}
\]
This retains the full lower-order normalization across the infinite product.
No Barnes asymptotic truncation is needed in (17); (13) has its own strict
integral remainder, and exact Barnes values give an independent check.

## 4. Elementary all-order corrections

The Barnes term has an ordinary expansion
\[
T_D(N)\sim\sum_{k\ge1}e_kN^{-k},
\]
whose first coefficients are
\[
\boxed{T_D(N)=-\frac1{8N}+\frac1{64N^2}+\frac1{192N^3}
-\frac1{256N^4}-\frac1{640N^5}
+\frac{17}{6144N^6}+\cdots.}
\tag{18}
\]
A rational all-order recurrence follows by taking the difference between
cutoffs \(N\) and \(N-1\). Set \(d_r=0\) for positive even \(r\).
For \(r\ge2\),
\[
\boxed{e_{r-1}=-\frac1{r-1}
\left[d_r+\frac1{4r}
+\sum_{k=1}^{r-2}\binom{r-1}{k-1}e_k\right].}
\tag{19}
\]
The defining difference is
\(T_D(N)-T_D(N-1)=\log D_N+\tfrac14\log[N/(N-1)]\), which proves
the recurrence.

For the complete normalized product, let \(L=\log(2\pi N)\).
Euler–Maclaurin applied to (15) gives
\[
\boxed{\begin{aligned}
\log S_N=\log K
&-\frac1N\left[\frac{2L^2+2L+1}{4\pi^2}+\frac18\right]\\
&+\frac1{N^2}\left[\frac{2L^2-2L-1}{8\pi^2}+\frac1{64}\right]
+O(L^4/N^3).
\end{aligned}}
\tag{20}
\]
For example the first radial integral is exactly
\[
\int_N^\infty\frac{2\log^2(2\pi x)-2\log(2\pi x)-1}
{4\pi^2x^2}\,dx
=\frac{2L^2+2L+1}{4\pi^2N}.
\]
The logarithmic radial correction is the leading finite-cutoff effect;
the plain Stirling term supplies the additional \(-1/(8N)\). Higher
polynomials follow mechanically from (15), the standard Hurwitz-zeta
Euler–Maclaurin expansion and (19). Formula (17) supplies the controlled
version at any chosen finite cutoff.

## 5. Directed computational record

`computations/verify_binomial_normalization.py` uses 384-bit directed Arb,
220 rational bisections for each of 1,024 radial roots, exact integer
central-binomial coefficients, and an independent 100-decimal evaluation.
It verifies (4) independently by the Barnes function at five cutoffs,
then checks (14) and (17) with \(M=J=4\).

| N | Direct \(S_N\), abbreviated |
|---:|---:|
|16|1.1199604511149576677684024230|
|64|1.1824249033291259912086026324|
|256|1.2094010315730541182146095779|
|512|1.2157987517054634222856193142|
|1024|1.2196435801184013439180897217|

At \(N=1024\), the Stirling-tail bound is below
\(3.464435\times10^{-28}\), the radial-tail bound is below
\(1.148215\times10^{-15}\), and the corrected product is enclosed by
\[
\boxed{K\in[1.22500170731420\ \pm\ 3.10\times10^{-15}].}
\tag{21}
\]
The separate closed-form evaluation of (2) is enclosed to more than 75
decimal places. The runtime was approximately two CPU seconds. The JSON
record retains all constants, cutoff values, error bounds, exact formal
coefficients, a checksum of every rational root bracket and the frozen
input provenance.

The companion [deformed-zeta note](binomial-deformed-zeta.md) promotes
\(C_n\) into a two-variable Dirichlet deformation and evaluates the
zeta determinant of the effective spectrum \(nC_n\) exactly.
