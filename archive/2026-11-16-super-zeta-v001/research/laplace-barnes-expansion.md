# The Laplace fold controls a convergent hierarchy of multiple zeta coefficients

16 November 2026. The inverse-cosine critical value has an exact additional
role: it controls the uniform logarithmic inverse-coupling expansion of the
relative superzeta and its coefficient hierarchy. Its coefficients are classical alternating
Barnes–Euler multiple zeta values, reducing explicitly to finite combinations
of Dirichlet eta values.

## 1. The exact coupling threshold

The current unshifted spectral function is
\[
\mathcal Z(s;\varepsilon)=2\pi^{-2s}(2^{2s}-1)\zeta(2s)
+\frac{s\sin\pi s}{\pi}\int_0^\infty
v^{-s-1}\log(1+r(v)/\varepsilon^2)dv,
\]
\[
r(v)=v\operatorname{sech}^2\sqrt v.
\]
At v=x²,
\[
\frac d{dx}(x^2\operatorname{sech}^2x)
=2x\operatorname{sech}^2x(1-x\tanh x).
\]
The function x tanh x strictly increases from zero to infinity. Let nu>0
be its unique root at one and put
\[
\boxed{R_{\rm L}=\nu/\cosh\nu,\qquad\nu\tanh\nu=1.}
\tag{1}
\]
Then max_(v>=0)r(v)=R_L². This is the established Laplace critical value
in the imaginary inverse-cosine section. For |epsilon|>R_L, the logarithmic
series is uniformly convergent over the entire positive integration ray.

## 2. The exact multiple-zeta coefficients

Define the alternating Barnes–Euler function in its absolutely convergent
half-plane Re p>N by
\[
\eta_N(p,a)=\sum_{k_1,\ldots,k_N\ge0}
\frac{(-1)^{k_1+\cdots+k_N}}{(a+k_1+\cdots+k_N)^p}.
\tag{2}
\]
This is the classical multiple Barnes–Euler definition, e.g.
[Hu–Kim, introduction](https://arxiv.org/pdf/1703.05434). Grouping by the
sum of the N indices gives the binomial degeneracy
\[
\eta_N(p,a)=\sum_{\ell\ge0}
(-1)^\ell\binom{N+\ell-1}{N-1}(a+\ell)^{-p}.
\]

For m>=1 define
\[
I_m(s)=\int_0^\infty v^{m-s-1}\operatorname{sech}^{2m}\sqrt v\,dv,
\qquad\Re s<m.
\]
Expanding sech^(2m)(x) after v=x², with absolute interchange first at
Re s<0, gives
\[
\boxed{I_m(s)=2^{2s+1}\Gamma(2m-2s)
\eta_{2m}(2m-2s,m).}
\tag{3}
\]
Analytic continuation extends the identity wherever the integral is analytic.

There is an explicit finite reduction. Let
\[
P_m(X)=X\prod_{j=1}^{m-1}(X^2-j^2)
=\sum_{j=0}^{m-1}c_{m,j}X^{2j+1}.
\]
For n>=m,
binom(n+m-1,2m-1)=P_m(n)/(2m-1)!; the polynomial vanishes at the positive
integers n<m. Thus, writing eta(q)=(1-2^(1-q))zeta(q) with its removable
value eta(1)=log2,
\[
\boxed{\eta_{2m}(p,m)=
\frac{(-1)^{m+1}}{(2m-1)!}
\sum_{j=0}^{m-1}c_{m,j}\eta(p-2j-1).}
\tag{4}
\]
For example,
\[
I_1(s)=2^{2s+1}\Gamma(2-2s)\eta(1-2s),
\]
\[
I_2(s)=\frac{2^{2s+1}\Gamma(4-2s)}6
[\eta(3-2s)-\eta(1-2s)].
\tag{5}
\]
At s=0 these become I1=2log2 and
I2=2[eta(3)-log2]. Higher orders use the same exact polynomial rule.

## 3. Convergent higher-zeta expansion and an explicit tail

For Re s<1 and |epsilon|>R_L,
\[
\boxed{J(s;\varepsilon)=\frac{s\sin\pi s}{\pi}
\sum_{m\ge1}\frac{(-1)^{m-1}}{m\varepsilon^{2m}}I_m(s).}
\tag{6}
\]
To justify normal interchange, put sigma=Re s and q=R_L²/|epsilon|²<1.
Positivity and the maximum in (1) give
\[
|I_m(s)|\le I_m(\sigma)
\le R_L^{2(m-1)}I_1(\sigma).
\]
After retaining m=1,...,M, the absolute error is bounded by
\[
\boxed{\left|\frac{s\sin\pi s}{\pi}\right|
\frac{I_1(\sigma)}{|\varepsilon|^2}
\frac{q^M}{(M+1)(1-q)}.}
\tag{7}
\]
This gives a controlled multiple-zeta computation of the original epsilon=1
relative correction. The actual root R_L is below one, so that coupling lies
strictly in the convergence domain.

At the spectral origin, the coefficient of s² is
\[
\int_0^\infty\frac{\log(1+r(v)/\varepsilon^2)}v\,dv
=\sum_{m\ge1}\frac{(-1)^{m-1}I_m(0)}{m\varepsilon^{2m}}.
\tag{8}
\]
Its coefficients are finite rational combinations of log2 and odd Dirichlet
eta values by (4). Equation (8) computes the extra curvature of the spectral
zeta at zero; the determinant value remains fixed at four.

The inverse-function fold, the integral's global maximum, and the convergence
radius of this hierarchy are therefore the same exact quantity. The complex
coupling singularities of the integrand occur at
epsilon=±i sqrt(r(v)); the endpoints are ±iR_L, matching the Laplace section.

## 4. A universal Gaussian curvature and a square-root branch

Let g(x)=log(x²sech²x). At its maximum x=nu, equation (1) gives
\[
\boxed{g''(\nu)=-2/\nu^2-2\operatorname{sech}^2\nu=-2.}
\]
The Laplace method applied to I_m(s)=2integral x^(-2s-1)exp(mg(x))dx gives
\[
\boxed{I_m(s)\sim2\sqrt\pi\,\nu^{-2s-1}
R_L^{2m}m^{-1/2}.}
\tag{9}
\]
The asymptotic is uniform on compact s-sets. For s=0 the positive coefficient
root limit proves that the curvature series (8), in beta=epsilon^-2, has
radius exactly R_L^-2. This describes the coefficient hierarchy; at
nonpositive integer s the prefactor in (6) may cancel the specialization.

There is also a precise fold singularity. For Re s<1 set
\[
\mathcal F_s(X)=\int_0^\infty v^{-s-1}
\log\left(1-X\frac{r(v)}{R_L^2}\right)dv.
\]
It has a finite real-side limit at X=1 and, as real X increases to one,
\[
\boxed{\mathcal F_s(X)=\mathcal F_s(1)
+4\pi\nu^{-2s-1}\sqrt{1-X}+O(1-X).}
\tag{10}
\]
To see the coefficient, use an analytic Morse coordinate u near x=nu with
r(x²)/R_L²=1-u². The measure v^(-s-1)dv has value
2nu^(-2s-1)du at u=0 because g''(nu)=-2. The local logarithm difference
has leading integral integral_R log(1+delta/u²)du=2pi sqrt(delta).
Odd amplitude terms cancel on a symmetric local interval; its remaining
terms and the outside region contribute O(delta). This proves (10).
It continues to a slit neighborhood with the selected square-root branch.

## 5. Reproduction

`computations/verify_superzeta_residues.py` checks the residue probabilities,
shifted determinant and trace identities. `verify_laplace_barnes.py` checks
the polynomial degeneracies, coefficient integrals, Laplace root isolation,
convergent coupling sums and their explicit remainder against independently
computed spectral integrals. Precision and point/directed scope are retained
in their JSON records.

The retained replay uses a 400-step exact rational isolation of nu with
512-bit directed signs. Barnes coefficients are evaluated as 832-bit balls,
with an independent cache of 73 Dirichlet-eta point values at 250 decimal
digits to control cancellation. It checks 882 exact polynomial degeneracy
values and 252 alternating signs through m=36. Twelve coefficient integrals
at m=1,2,3,6 and s=-1/4,1/4,3/4 use independent 90-digit point quadrature,
the fourth-power endpoint substitution, cutoff x=120 and an explicit
exponentially small analytic tail. Their largest point discrepancy is below
3.30 x 10^-91.

For epsilon=1,2, the same three s-values and cutoffs M=12,36, the directed
finite eta sums plus (7) enclose the complete independently retained
512-bit Mellin reference intervals. At M=36 the largest written tail is
below 4.250 x 10^-15 for epsilon=1 and 1.418 x 10^-37 for epsilon=2.
The reference `cosine-spectrum-results.json` is frozen under
`sources/foundation/`; its origin, SHA256 and byte count are recorded, and
the script verifies that hash before using it.

Positive point quadrature checks (9) at m=16,32,64 for s=0 and s=1/4,
using 90 digits and cutoff x=40 with a written analytic tail. At s=0
the ratios to the proved leading term are approximately 1.0042023294,
1.0020990162 and 1.0010489639. These are point checks of the analytic
asymptotic theorem. The coupling enclosures above combine directed finite
sums and directed analytic remainder bounds. The full retained run took
about 1.82 CPU seconds.
