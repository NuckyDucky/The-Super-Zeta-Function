# Reciprocal dynamics, renormalized products, and exact zeta bridges

## Source reconstruction and scope

The exact requested PDFs are present at:

- `Dottie_Parabolic_Quantization_Preprint_v0.4.pdf` (21 pages, internally v0.4, August 7, 2026).
- `Reciprocal_Tetration_Logarithmic_Lift_Preprint_v0.10.pdf` (31 pages; its internal title page says draft v0.9, August 6, 2026).

Both were extracted and their relevant mathematical pages and figures reviewed. The Dottie PDF's Figure 1 displays the centerline period normalization; Figure 2 marks the Dottie tip and neighboring spire components. The lift PDF's Figure 1 displays the positive fixed-pair curve and its reciprocal extrema. The exact Touchard formulas were read from rendered page 3 of the Dottie PDF, including the normalization factors.

The v0.4 Dottie paper separates exact local identities from the log-free even-transit hypothesis used for its finite-period correction architecture. This report uses the exact fixed-pair and germ identities. Its new transcendence deductions have their own stated assumptions. The preprint's numerical chamber and horn observables retain their original measured/conditional statuses.

Original materials remain unchanged. New scripts, extracted text, selected page renders, and experiment results are in the separate research tree. The numerical work below runs at 100 and 200 decimal digits; all reported 75-digit outputs agree.

## 1. Fixed-pair coordinates that expose the number theory

For L nonzero, a fixed pair satisfies

\[
P=e^{LM},\qquad M=e^{-LP}.
\]

Use the actual lifted logarithmic coordinates

\[
U=LM,\qquad V=-LP.
\]

They satisfy the exact identities

\[
P=e^U,\quad M=e^V,\quad UP+VM=0,
\quad \mu=-L^2PM=UV.
\tag{1}
\]

U,V are logarithms selected by the dynamical equations; this specifies branches even when principal logarithms differ by multiples of 2*pi*i. Dividing compatibility gives

\[
\frac PM=-\frac VU,
\qquad e^{U-V}=-\frac VU.
\tag{2}
\]

The preprint's Lambert atlas follows by setting x=Ue^U=-Ve^V:

\[
U=W_k(x),\quad V=W_m(-x),\quad
L=-UV/x.
\]

For a prescribed nonzero multiplier mu, the branch locus is

\[
W_k(-\mu/L)W_m(\mu/L)=\mu.
\]

This is the correct starting point for arithmetic questions about a fixed pair.

## 2. A complete algebraic-phase classification on the positive curve

**DP-1 (proved application of Gelfond-Schneider, with an alternative Baker proof).** A positive fixed pair has both coordinates algebraic exactly when its ratio r=P/M is rational.

The exact positive parametrization, already present in the preprints, becomes

\[
P=r^{1/(1+r)},\qquad M=r^{-r/(1+r)},\qquad
L=\frac{\log r}{P+M},\qquad r>0.
\tag{3}
\]

For rational r the exponents are rational, so both phases are algebraic. Conversely, algebraic P,M give algebraic r. If r were algebraic irrational, the exponent 1/(1+r) would be algebraic irrational and Gelfond-Schneider would make P transcendental. Thus r is rational. This proves the equivalence using Gelfond-Schneider alone.

Baker supplies a second proof that also explains the logarithmic structure. Suppose P,M are algebraic and the pair is nontrivial. Their real logarithms obey

\[
P\log P+M\log M=0.
\]

Baker's theorem says that logarithms of algebraic numbers which are rationally linearly independent remain linearly independent over the algebraic numbers. Thus these two logarithms are rationally dependent. Compatibility then gives log(P)/log(M)=-M/P, which is rational. Hence r is rational. The trivial pair P=M=1 corresponds to r=1,L=0.

There are sharper consequences:

- If r is algebraic irrational, both exponents in (3) are algebraic irrational, so **both phases are transcendental** by Gelfond-Schneider.
- For rational r other than 1, **L and the visible base exp(L) are transcendental**.

Here is the argument for the second assertion. The only positive rational pair satisfying compatibility is (1,1). After interchanging the phase names if necessary, any nontrivial such pair would have P=q^m, M=q^(-n), with q=a/b>1 rational in lowest terms and m,n positive coprime integers. Compatibility gives q^(m+n)=n/m. Unique factorization yields n=a^(m+n),m=b^(m+n), and a>=2 makes n>=2^(m+n)>n, a contradiction. Consequently the algebraic number P+M is irrational when r is rational other than 1. L is a nonzero algebraic multiple of log(r), hence transcendental by Lindemann-Weierstrass. Finally

\[
e^L=r^{1/(P+M)}
\]

is transcendental by Gelfond-Schneider.

This is an exact arithmetic classification of a curve from Nick's project. For example r=2 gives P=2^(1/3),M=2^(-2/3), while the generating lift and base are transcendental. The experiment records r=2,3/2,sqrt(2) and verifies the fixed equations at both precisions.

The classical theorem statements and original references are collected in `classical-theory-report.md`; DP-1 is a specialization derived here.

## 3. Algebraic multipliers force transcendental orbit values

**DP-2 (proved application of Lindemann-Weierstrass).** Consider a cyclic signed exponential system

\[
X_j=\exp(s_j L X_{j+1}),\quad s_j\in\{1,-1\},\quad
j\pmod r,
\]

with L nonzero and nonzero algebraic return multiplier

\[
\mu=L^r\left(\prod_j s_j\right)\left(\prod_j X_j\right).
\tag{4}
\]

At least one cycle coordinate is transcendental.

Proof: if every X_j were algebraic, (4) would make L^r algebraic and hence L algebraic. Each nonzero algebraic exponent s_j L X_(j+1) would then have transcendental exponential, contradicting the algebraic value X_j. This uses the exact derivative product for the return map.

For the reciprocal fixed pair the relevant scalar multiplier is mu=-L^2PM. Thus an algebraic nonzero multiplier forces a transcendental phase. At the Dottie point M is the complex conjugate of P; algebraicity is preserved by complex conjugation, so **both Dottie phases are transcendental**.

**DP-3 (proved).** If a reciprocal fixed pair has nonzero algebraic mu, then its lifted logarithms U,V are transcendental and rationally linearly independent.

If U were algebraic, V=mu/U would be algebraic. Equation (2) and Lindemann-Weierstrass would force U=V, while compatibility would force 2Ue^U=0. The nonzero coordinates exclude that case. Rational dependence V=qU would make U^2=mu/q algebraic, giving the same contradiction.

## 4. A concrete restricted consequence of Schanuel

**DP-4 (conditional on Schanuel for U,V).** At every reciprocal fixed pair with nonzero algebraic multiplier, P,M are algebraically independent. The pair U,L is also algebraically independent.

DP-3 supplies the rational linear independence required by Schanuel. Therefore

\[
\operatorname{trdeg}_{\mathbb Q}
\mathbb Q(U,V,e^U,e^V)\ge2.
\]

Over the algebraic numbers, (1)-(2) give

\[
V=\mu/U,\qquad U^2=-\mu M/P.
\]

Thus adjoining U,V to P,M is algebraic, and P,M have transcendence degree two. Also

\[
P=-\frac{\mu}{LU},\qquad M=\frac UL,
\qquad L^2=-\frac\mu{PM}.
\]

These equations transfer that transcendence degree to U,L.

At the Dottie point, set d=cos(d), s=sin(d), y*=exp(-s). The exact preprint identities are

\[
U=\alpha=s+id=i e^{-id},\quad V=1/\alpha=s-id,
\quad L=i y_*,\quad \mu=1.
\]

Since

\[
d=\frac{\alpha-\alpha^{-1}}{2i},
\qquad \alpha^2-2id\alpha-1=0,
\]

Q(alpha) and Q(d) have the same transcendence degree after adjoining algebraic i. DP-4 therefore yields the precise restricted statement

\[
\boxed{\text{Schanuel implies that }d\text{ and }e^{-\sin d}
\text{ are algebraically independent}.}
\tag{5}
\]

This is a direct connection between the conjecture and the project's distinguished parameter.

## 5. Touchard coefficients: unconditional arithmetic information

The preprint's exact normalized germ is

\[
F_\alpha(x)=\frac{1+\alpha}{2\alpha}
\left[\exp\!\left(\alpha(e^{2x/(1+\alpha)}-1)\right)-1\right],
\]

with coefficients

\[
h_n(\alpha)=\frac{2^{n-1}T_n(\alpha)}{n!\alpha(1+\alpha)^{n-1}},
\quad F_\alpha(x)=x+x^2+h_3x^3+\cdots.
\tag{6}
\]

**DP-5 (proved).** At the Dottie parameter every h_n for n>=3 is transcendental. The iterative residue rho is transcendental too.

First d is transcendental: algebraic nonzero d would give an algebraic-coefficient linear relation among 1,exp(id),exp(-id) through cos(d)=d, contrary to Lindemann-Weierstrass. Then sin(d) is transcendental because sin(d)^2+d^2=1. The imaginary part of alpha is d, so alpha is transcendental.

For n>=3 the rational function h_n(alpha) is nonconstant. In T_n(alpha)/alpha the coefficient of alpha^(n-2) is the Stirling number S(n,n-1)=n(n-1)/2, whereas in (1+alpha)^(n-1) it is n-1. These differ for n>=3. A nonconstant rational function with rational coefficients evaluated at a transcendental number is transcendental. This proves the coefficient claim.

The residue has the exact expression

\[
\rho=\frac{\sin d}{3(1+\sin d)},
\]

another nonconstant rational function of a transcendental number.

There is also a finite reconstruction of the germ parameter. Let

\[
w=\frac{24h_4-22+42\rho}{6\rho-2}.
\]

Then exact simplification gives

\[
w=\frac{\alpha-1}{\alpha+1},\qquad
\alpha=\frac{1+w}{1-w}.
\tag{7}
\]

The Dottie values avoid the displayed exceptional denominators. Thus the first two higher coefficients already recover alpha rationally: Q(h_3,h_4)=Q(alpha). The script verifies (7) symbolically and records h_3 through h_12. The all-order transcendence argument is the coefficient comparison above.

For functional independence, see `ax-functional-report.md`. There Ax's theorem gives algebraic independence of the variable, the first exponential, and g_L of the variable for every fixed L nonzero; the same derivative calculation produces the Touchard hierarchy. Its exact differential equation is g g''-(g')^2+L g g'=0.

## 6. The exact four-/six-exponentials eligibility conditions

The most immediate two-by-two matrix from one reciprocal pair is

\[
\begin{pmatrix}
e^{LP}&e^{-LP}\\e^{LM}&e^{-LM}
\end{pmatrix}
=
\begin{pmatrix}M^{-1}&M\\P&P^{-1}\end{pmatrix}.
\]

Its exponential-grid column parameters are L and -L, which span one rational direction. For a four-exponentials application an additional column c must satisfy c/L irrational; its row parameters P,M must satisfy P/M irrational. The entries exp(cP),exp(cM) then become the additional arithmetic objects to control. If both original phases are algebraic, Baker forces P/M rational, as DP-1 demonstrates on the positive branch and the compatibility argument demonstrates with actual logarithmic branches in general.

The six-exponentials theorem similarly calls for three rationally independent column parameters, together with the two independent row parameters. These explicit rank conditions identify what a suitable deformation would have to supply. For varying L,z, Ax's Jacobian-rank theorem is directly productive; the companion report computes the required rank two.

## 7. The old Desmos product and an exact finite form

Define

\[
Q_N=e^{3/2}\prod_{n=2}^{N}e\left(1-\frac1{n^2}\right)^{n^2}.
\]

Collecting the powers of consecutive integers gives the finite identity

\[
\boxed{Q_N=
\frac{e^{N+1/2}(N!)^2}{2N^{2N+1}}
\left(1+\frac1N\right)^{N^2}.}
\tag{8}
\]

Stirling's formula now gives Q_N -> pi. More precisely,

\[
\log\frac{Q_N}{\pi}
=\frac1{2N}-\frac1{4N^2}+\frac7{36N^3}
-\frac1{6N^4}+\frac{13}{90N^5}+O(N^{-6}).
\tag{9}
\]

Equation (8) follows from telescoping log(n-1),log(n),log(n+1); equation (9) follows from the gamma asymptotic expansion and log(1+1/N). [NIST gamma asymptotics](https://dlmf.nist.gov/5.11).

The exact archived product appears in S. R. Holcombe's *A product representation for pi*, posted in 2012 and published in the American Mathematical Monthly 120 (2013), p.705. Allouche's 2022 paper, section 5, derives the same product using a triple-sine derivative. These provide a precise literature identification for that construction. [Holcombe original](https://arxiv.org/pdf/1204.2451), [Allouche original](https://arxiv.org/pdf/2205.09492).

## 8. A parameter family joining the product to zeta and triple sine

Define an entire product

\[
\mathcal F(z)=\prod_{n=2}^{\infty}
e^{z^2}\left(1-\frac{z^2}{n^2}\right)^{n^2}.
\tag{10}
\]

On compact sets its logarithmic tails are bounded by a constant times sum(n^-2), giving locally uniform convergence. Its zeros at z=+/-n, n>=2, have multiplicity n^2. In the zero-free disk |z|<2, with log(F(0))=0,

\[
\boxed{\log\mathcal F(z)
=-\sum_{k=2}^{\infty}\frac{\zeta(2k-2)-1}{k}z^{2k}.}
\tag{11}
\]

Termwise differentiation and the cotangent partial fraction yield

\[
\boxed{\frac{\mathcal F'(z)}{\mathcal F(z)}
=\pi z^2\cot(\pi z)-z+\frac{2z^3}{1-z^2}.}
\tag{12}
\]

The apparent singularities at z=+/-1 cancel. The values there give

\[
\mathcal F(1)=\pi e^{-3/2},\quad
(\log\mathcal F)'(1)=-3/2,\quad
(\log\mathcal F)''(1)=-7/4-\pi^2/3.
\tag{13}
\]

The cotangent identity is recorded by [NIST](https://dlmf.nist.gov/4.22). These are analytical consequences of (10).

With the Kurokawa triple-sine normalization used by Allouche,

\[
\boxed{\mathcal F(z)=\frac{S_3(z)}{(1-z^2)e^{3z^2/2}}.}
\tag{14}
\]

In particular S_3'(1)=-2*pi recovers the original product. The same literature gives a half-argument value involving zeta(3), so

\[
\mathcal F(1/2)=\frac43\,2^{1/4}
\exp\!\left(-\frac38-\frac{7\zeta(3)}{8\pi^2}\right).
\tag{15}
\]

[Allouche, section 5 and the preceding triple-sine evaluation](https://arxiv.org/pdf/2205.09492).

This bridge extends to a weight hierarchy. For integer m>=0 put J=floor((m+1)/2), and define

\[
\mathcal P_m(z)=\prod_{n=2}^{\infty}
\exp\!\left(\sum_{j=1}^{J}\frac{z^{2j}n^{m-2j}}j\right)
\left(1-\frac{z^2}{n^2}\right)^{n^m}.
\]

The exponential removes exactly the nonsummable logarithmic terms, and

\[
\log\mathcal P_m(z)
=-\sum_{k=J+1}^{\infty}\frac{\zeta(2k-m)-1}{k}z^{2k},
\qquad |z|<2.
\tag{16}
\]

Holcombe's June 2026 preprint *A Regularised Wallis Hierarchy* studies this precise weighted-product program. The full paper was accessed through its PDF mirror. [Original paper, arXiv:2606.23973](https://pdfs.assets.alphaxiv.org/2606.23973v1.pdf).

## 9. A second exact zeta bridge already inside the Dottie preprint

The Dottie paper's section 11 uses Cohen's Lambert-branch determinant. For x=-1/L define

\[
D_L(t)=e^{-t/2}(1+Lte^t).
\]

Its zeros are W_k(-1/L). Cohen proves the symmetrically indexed product representation and the associated genus-one canonical product. [Cohen, theorem 2.2 and corollaries 2.3–2.4](https://arxiv.org/pdf/2012.11698).

Dividing by the undeformed lattice determinant gives

\[
\boxed{\frac{D_L(t)}{\sinh(t/2)/(t/2)}
=\frac{t}{e^t-1}(1+Lte^t).}
\tag{17}
\]

The Bernoulli factor t/(exp(t)-1) therefore belongs directly to the project. Its undeformed lattice moments are

\[
\sum_{k\ne0}(2\pi i k)^{-2m}
=-\frac{B_{2m}}{(2m)!},
\]

equivalent to Euler's even-zeta evaluation.

For the deformed roots, define Z_n as the inverse-power branch sum (symmetric principal value for n=1). The generating identity is

\[
\sum_{n\ge1}\frac{Z_n(L)}n t^n
=\frac t2-\log(1+Lte^t).
\]

Expanding the right side gives the full explicit polynomial family

\[
\boxed{Z_n(L)=\frac{\delta_{n1}}2+
\sum_{j=1}^{n}(-1)^j\frac nj
\frac{j^{n-j}}{(n-j)!}L^j.}
\tag{18}
\]

The first cases are Z_1=1/2-L, Z_2=L^2-2L, Z_3=-L^3+3L^2-3L/2. The new experiment verifies (18) symbolically through n=12. This is a concrete coefficient formula extending the low-order list in the preprint.

An arithmetic consequence is useful: for nonzero algebraic L, every individual W_k(-1/L) is transcendental by Lindemann-Weierstrass, while all polynomial moments Z_n(L) are algebraic. The exact infinite sum can therefore have simpler arithmetic than its separate branch values.

## 10. Theta, Mellin transforms, and completed zeta

Let theta(t)=sum over all integers n of exp(-pi*n^2*t), t>0. Poisson summation gives theta(t)=t^(-1/2)theta(1/t). Mellin transformation yields

\[
\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)
=\frac12\int_0^\infty(\theta(t)-1)t^{s/2-1}\,dt,
\quad \Re s>1.
\]

Splitting at 1 and using the theta transformation gives the meromorphic continuation

\[
\boxed{\Lambda(s)=\frac1{s(s-1)}+
\frac12\int_1^\infty(\theta(t)-1)
\bigl(t^{s/2}+t^{(1-s)/2}\bigr)\frac{dt}{t}.}
\tag{19}
\]

The symmetry s -> 1-s is explicit. Multiplying by s(s-1)/2 gives the entire completed xi function. These identities connect Gaussian/exponential kernels, the gamma normalization, pi, modular inversion, and zeta in a single exact construction. [NIST theta transformations](https://dlmf.nist.gov/20.7), [zeta integral representations](https://dlmf.nist.gov/25.5), [zeta reflection formulas](https://dlmf.nist.gov/25.4).

The experiment evaluates (19) as a rapidly convergent sum of incomplete gamma functions and compares it with pi^(-s/2)*Gamma(s/2)*zeta(s) at s=2,1/2+14i,3-4i. All 75 displayed digits agree between 100- and 200-digit working precision. The construction identifies the functional-equation bridge; the location of the nontrivial zeros is a further question about this same entire function.

## 11. Reproduction and next exact tasks

`dynamics-products/experiments.py` regenerates `results.json`, `precision100.json`, `precision200.json`, and `input-config.json`. Its symbolic checks include the product derivatives at z=1, the full moment formula through order12, the Touchard rational coefficient formulas, and the finite germ-parameter recovery (7). Its numerical checks include the finite-product telescope, parameter product and independent Hurwitz-tail evaluation, three exact fixed-pair examples, the Dottie identities, and theta-Mellin continuation.

`dynamics-products/plot_products.py` produces the standalone PNG/SVG figure `product-structure` and its numerical data. The left panel compares (8) with the acceleration obtained by removing the first three terms of (9): the relative errors have leading orders 1/(2N) and 1/(6N^4). The right panel shows the parameter family (10) and marks its z=1 value. The plot was visually inspected after rendering.

The most accessible next tasks are:

1. Write DP-1 and DP-2 as short standalone propositions linked to the fixed-pair curve and periodic sign words.
2. Apply Ax's theorem to parameter deformations using the exact Touchard germ; the companion Ax report supplies the functional rank calculations.
3. Study the parameterized product (10) as a normalized triple sine and use (12) to obtain further exact local values and interpolation functions.
4. Investigate the moment polynomial family (18) and the Dottie branch-dominance criterion using Cohen's determinant as the precise analytic object.
5. Keep the Dottie germ's exact coefficient field separate from the measured global horn and chamber quantities when designing new arithmetic experiments.

The labels DP-1 through DP-5 identify applications proved in this research note. Published priority for these particular formulations is a separate bibliography task; the cited classical theorems and the exact local identities make the mathematical derivations traceable.
