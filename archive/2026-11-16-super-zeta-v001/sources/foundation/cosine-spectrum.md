# The quartet spectrum is an explicit Fredholm spectrum

**Exact quotient, a boundary operator, canonical product, rational trace sums,
and a two-variable spectral zeta. 16 November 2026.**

The reciprocal phase equation has a particularly useful spectral coordinate:

\[
\boxed{u=\frac{\alpha-\alpha^{-1}}{2i}.}
\]

It turns the complete parabolic spectrum into the zeros of
\(\cos^2u-u^2\). Those zeros are the eigenvalues, up to the natural sign
pairing, of a concrete first-order boundary operator. Its inverse square is
trace class and has an elementary Fredholm determinant. A coupling deformation
then gives a genuine two-variable zeta whose entire correction to a shifted
Riemann zeta is an explicit Mellin integral.

## 1. Exact recovery of every ordered phase and parameter

The reciprocal fixed-pair compatibility at multiplier one is

\[
\alpha^2e^{\alpha-1/\alpha}=-1,\qquad
U=\alpha,\quad V=\alpha^{-1},\quad
L=-e^{-\alpha}/\alpha.
\tag{1}
\]

Put \(u=(\alpha-\alpha^{-1})/(2i)\). Equation (1) says
\(\alpha e^{iu}=\sigma i\) for a unique \(\sigma\in\{1,-1\}\).
Substitution into the defining equation for u gives

\[
\boxed{u=\sigma\cos u.}
\tag{2}
\]

Conversely, every zero of \(D(u)=\cos^2u-u^2\) has \(u\ne0\) and a unique
\(\sigma=\cos u/u\in\{1,-1\}\). Its exact recovery is

\[
\boxed{\alpha=\sigma i e^{-iu}=\sigma\sin u+iu,\qquad
\alpha^{-1}=\sigma\sin u-iu,\qquad
L=\sigma i e^{-\sigma\sin u}.}
\tag{3}
\]

Indeed the two phase expressions have product \(\sin^2u+u^2=1\), by (2),
and \(\alpha^2e^{2iu}=-1\). Formula (3) for L follows immediately from (1).
This proves a bijection between D-zeros and ordered parabolic phases.
The algebraic map u has two preimages on the whole punctured alpha-plane;
equation (3) selects its unique preimage on the compatibility locus.

For the positive Dottie root \(d=\cos d\), equation (3) is
\(\alpha=\sin d+id\), \(L=ie^{-\sin d}\). The entire nonunit spectrum is
therefore part of the same complex cosine-fixed-point family.

The reciprocal and conjugation operations become

\[
\alpha\mapsto\alpha^{-1}\quad\longleftrightarrow\quad u\mapsto-u,
\]
\[
\alpha\mapsto\bar\alpha\quad\longleftrightarrow\quad u\mapsto-\bar u.
\tag{4}
\]

Thus the two sign choices form the Klein four-group acting by sign and
conjugation on the u-plane. Their actions on L remain the actual sign and
conjugation actions already proved in the quartet classification.

For the nonunit phase \(e^{t_n+i\theta_n}\), the representative is

\[
u_n=x_n+it_n,\qquad
x_n=\cosh t_n\sin\theta_n=(n+\tfrac12)\pi-\theta_n.
\tag{5}
\]

In particular \((n-1/2)\pi<x_n<n\pi\), and
\(u_n=\pi n+i\log(2\pi n)+O(\log n/n)\). The complete D-zero set is
\(\pm d\) and \(\pm u_n,\pm\bar u_n\), n>=1. All are simple: a multiple
zero would give \(\sigma\sin u=-1\), hence \(u^2=0\), contradicting (2).

## 2. A boundary operator with compact inverse and the cosine spectrum

Let \(\mathcal H=L^2(-1,1)\oplus\mathbb C\). For a nonzero coupling
\(\varepsilon\), define

\[
\mathcal A_\varepsilon(f,c)=
\left(-if',\ \frac\varepsilon2[f(1)+f(-1)]\right),
\quad
\mathcal D(\mathcal A_\varepsilon)
=\{(f,c):f\in H^1(-1,1),\ c=f(0)\}.
\tag{6}
\]

The domain is dense: an arbitrarily narrow smooth bump about zero can prescribe
its point value while changing its L2 norm arbitrarily little. The operator
is closed, since its graph controls the H1 norm and the trace values.

The eigenvalue equation gives \(f(x)=c e^{iux}\) and

\[
\boxed{u=\varepsilon\cos u.}
\tag{7}
\]

If c vanished, the eigenfunction would vanish. Solving at u=0 gives the bounded
inverse explicitly:

\[
\boxed{\mathcal B_\varepsilon(h,k)=
\left(\frac i2\int_{-1}^1\operatorname{sgn}(x-t)h(t)dt+
\frac{k}{\varepsilon},\quad
\frac{k}{\varepsilon}-\frac i2\int_{-1}^1\operatorname{sgn}(t)h(t)dt\right).}
\tag{8}
\]

It maps into the domain in (6), and direct differentiation/boundary evaluation
checks both inverse identities. The integral block is Hilbert–Schmidt and
the remaining blocks have finite rank. In fact

\[
\boxed{\|\mathcal B_\varepsilon\|_2^2
=\frac32+\frac3{|\varepsilon|^2}.}
\tag{9}
\]

Thus \(\mathcal B_\varepsilon^2\) is trace class. The nonzero compact
spectrum and the eigenvalue equation completely specify the reciprocal
eigenvalues. Generalized multiplicities agree with those of
\(\cos u-u/\varepsilon\), as follows either from the explicit resolvent
or the determinant identity proved next.

## 3. Exact Fredholm determinant and controlled finite matrices

**Theorem.** With the usual second regularized determinant,

\[
\boxed{\det{}_2(I-u\mathcal B_\varepsilon)
=e^{u/\varepsilon}(\cos u-u/\varepsilon),}
\tag{10}
\]

and the ordinary trace-class determinant is

\[
\boxed{\det(I-\lambda\mathcal B_\varepsilon^2)
=E_\varepsilon(\lambda)
:=\cos^2\sqrt\lambda-\lambda/\varepsilon^2.}
\tag{11}
\]

The expression on the right is entire in lambda: its power series removes
the square root. At epsilon=1 its zeros encode every original parabolic
phase and parameter through (3) and sign pairing.

**Proof by explicit projection.** Partition (-1,1) into an even number N of
equal cells. Project the L2 component onto its cellwise constants and retain
the scalar component. In the orthonormal basis, the finite matrix has blocks

\[
(B_N)_{jk}=\frac iN\operatorname{sgn}(j-k),\quad
(B_N)_{j,N+1}=\frac{\sqrt{2/N}}\varepsilon,
\]
\[
(B_N)_{N+1,j}=-\frac i2\sqrt{2/N}\,s_j,\quad
(B_N)_{N+1,N+1}=1/\varepsilon,
\]

where s_j is -1 on the first half and +1 on the second half.
Only the integral kernel's diagonal cells contribute to projection error:

\[
\|\mathcal B_\varepsilon-B_N\|_2^2=1/N.
\tag{12}
\]

Finite elimination gives

\[
\delta_{N,\varepsilon}(u):=\det(I-uB_N)
=\frac{(1+iu/N)^N+(1-iu/N)^N}{2}
-\frac u\varepsilon(1+u^2/N^2)^{N/2}.
\tag{13}
\]

One may derive (13) by subtracting consecutive integral rows: their successive
homogeneous values have ratio (1+iu/N)/(1-iu/N). The two half-interval
transfers have N/2 steps. Substitution into the retained midpoint boundary row
gives the numerator in (13); the cell factors clear the transfer denominators.
Equivalently, the integral block determinant is the first term in (13), and
its rank-one boundary Schur complement contributes the second term. These
identities are polynomial, so the intermediate exceptional denominator values
are covered by polynomial continuation.

Since tr(B_N)=1/epsilon, its regularized determinant is
exp(u/epsilon) delta_N,epsilon(u). Formula (13) converges locally uniformly
to cos(u)-u/epsilon. Hilbert–Schmidt continuity of det2 and (12) give (10).
Multiplying (10) at u and -u cancels the exponentials and gives (11): at the
eigenvalue-product level, each pair of regularized factors becomes
1-u² nu². This also follows by trace-class convergence of B_N² to B². ∎

The determinant conventions and projection framework are classical; see
[Bornemann (2010), §§2–5](https://arxiv.org/pdf/0804.2543).
Here the boundary operator, finite formula and error constants are derived
for the cosine/quartet family.

### A useful all-N numerical bound

For |u|<=r<N, put

\[
\eta_N=\frac{r^3}{3N^2(1-r/N)},\qquad
\widetilde\eta_N=\frac{r^4}{4N^3(1-r^2/N^2)},
\]

\[
e_N=e^r(e^{\eta_N}-1)+\frac r{|\varepsilon|}
(e^{\widetilde\eta_N}-1),\qquad
M=e^r+r/|\varepsilon|.
\]

The logarithmic Taylor remainders of the two factors in (13) give

\[
\boxed{|e^{-u^2/(2N)}\delta_{N,\varepsilon}(u)
-(\cos u-u/\varepsilon)|\le e_N,}
\tag{14}
\]

\[
\boxed{|e^{-\lambda/N}\det(I-\lambda B_N^2)-E_\varepsilon(\lambda)|
\le e_N(2M+e_N),\quad |\lambda|\le r^2.}
\tag{15}
\]

This is a controlled O(N^-2) approximation after the explicit trace
counterterm. The uncorrected matrices have
tr(B_N²)=1+epsilon^-2-1/N, explaining that counterterm directly.

## 4. Canonical product and exact rational trace sums

At epsilon=1, E has order 1/2 and E(0)=1. The trace-class determinant gives
the absolutely locally convergent product

\[
\boxed{E(\lambda)=
\left(1-\frac\lambda{d^2}\right)
\prod_{n\ge1}
\left(1-\frac\lambda{u_n^2}\right)
\left(1-\frac\lambda{\bar u_n^2}\right).}
\tag{16}
\]

Its logarithmic coefficients are exact power traces:

\[
\mathcal Z(m;1)=\operatorname{tr}(\mathcal B_1^{2m})
=d^{-2m}+2\Re\sum_{n\ge1}u_n^{-2m}.
\]

Since
\[
E_\varepsilon(\lambda)
=1-(1+\varepsilon^{-2})\lambda+
\sum_{m\ge2}\frac{(-1)^m2^{2m-1}}{(2m)!}\lambda^m,
\]
Newton identities show every positive-integer trace is in
\(\mathbb Q[\varepsilon^{-2}]\). At epsilon=1:

\[
\boxed{\mathcal Z(1)=2,\quad\mathcal Z(2)=10/3,\quad
\mathcal Z(3)=92/15,\quad\mathcal Z(4)=3538/315.}
\tag{17}
\]

The first identity explicitly couples Dottie to every nonunit quartet:
\[
\boxed{d^{-2}+2\Re\sum_{n\ge1}(x_n+it_n)^{-2}=2.}
\tag{18}
\]
For m>=1 and N>=1, equation (5) gives a simple rigorous tail:
\[
\left|2\Re\sum_{n>N}u_n^{-2m}\right|
\le\frac{2\pi^{-2m}}{2m-1}(N-1/2)^{1-2m}.
\tag{19}
\]

## 5. A two-variable zeta for the inverse-cosine coupling family

For epsilon>0, enumerate the zeros lambda_j of E_epsilon with algebraic
multiplicity, and use their principal logarithms. E_epsilon(-t)>0 for t>=0,
so the negative real axis is an admissible spectral cut. Define

\[
\boxed{\mathcal Z(s;\varepsilon)=\sum_j\lambda_j^{-s},
\qquad\Re s>1/2.}
\tag{20}
\]

The order-1/2 entire function gives absolute convergence in that half-plane.
More explicitly, the bound
|E_epsilon(lambda)|<=C(1+|lambda|)exp(2sqrt|lambda|) and Jensen's formula
give a zero count O(sqrt R). At a zero, with u²=lambda, equation (7) gives
|u|=epsilon|cos u|>=epsilon sinh|Im u|, hence
|Im u|<=asinh(|u|/epsilon)=O(log|u|). Consequently the large lambda
zeros approach the positive-axis sector; the finitely many remaining zeros
stay off the negative axis. This uniform sector control and the absolutely
summable |lambda_j|^-Re(s) justify interchange with the Stieltjes integral.
The determinant and principal-cut
Stieltjes identity give, initially for 1/2<Re s<1,

\[
\mathcal Z(s;\varepsilon)
=\frac{\sin\pi s}{\pi}
\int_0^\infty t^{-s}\frac d{dt}\log E_\varepsilon(-t)dt.
\]

Use the exact factorization
\[
E_\varepsilon(-t)=\cosh^2\sqrt t
\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right).
\]
The cosh factor has the double reference spectrum
[(n+1/2)pi]^2, n>=0. Integrating the relative part by parts yields

\[
\boxed{\mathcal Z(s;\varepsilon)
=2\pi^{-2s}(2^{2s}-1)\zeta(2s)+J(s;\varepsilon),}
\tag{21}
\]

\[
\boxed{J(s;\varepsilon)=\frac{s\sin\pi s}{\pi}
\int_0^\infty t^{-s-1}
\log\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right)dt.}
\tag{22}
\]

The integral in (22) converges throughout Re s<1. At infinity its integrand
decays exponentially in sqrt(t). At zero its logarithm has a convergent
Taylor series sum_{m>=1}c_m t^m. Splitting at any sufficiently small a>0
and subtracting its first M terms gives

\[
\int_0^a t^{-s-1}\left(F(t)-\sum_{m=1}^Mc_mt^m\right)dt
+\sum_{m=1}^M\frac{c_ma^{m-s}}{m-s}
+\int_a^\infty t^{-s-1}F(t)dt.
\tag{23}
\]

This continues the integral to Re s<M+1 with simple possible poles at the
positive integers. The factor sin(pi s) cancels each pole. Thus J is entire.
This is the endpoint-subtraction Mellin method of
[NIST DLMF §2.5](https://dlmf.nist.gov/2.5), applied here to the displayed
relative determinant.

**Corollary.** For every epsilon>0:

\[
\boxed{\operatorname*{Res}_{s=1/2}\mathcal Z(s;\varepsilon)=1/\pi,}
\]
\[
\boxed{\mathcal Z(-m;\varepsilon)=0\quad(m=0,1,2,\ldots),}
\]
\[
\boxed{\mathcal Z'(0;\varepsilon)=-\log4,
\qquad\det{}_\zeta(\mathcal A_\varepsilon^2)=4.}
\tag{24}
\]

Indeed the reference zeta has its single pole at 1/2 and zeros at the
nonpositive integers. For the latter, sin(pi s) vanishes in the convergent
relative integral; at zero J has a double zero. The reference derivative is
2[2log(2) zeta(0)]=-log(4). In particular the regularized determinant is
constant along this coupling family even while its individual eigenvalues move.
For shifts lambda near zero with consistent spectral cuts, the zeta determinant
is therefore 4 E_epsilon(lambda), and this expression continues it as an
entire determinant in lambda.

An additional computable relative invariant is
\[
\partial_s^2J(0;\varepsilon)=
2\int_0^\infty\frac1t
\log\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right)dt>0.
\tag{25}
\]

### Holomorphic complex coupling domain

Equations (21)–(24) extend jointly to all complex couplings
\(\Re\varepsilon>0\). For c=t sech²(sqrt(t))>=0, the argument
1+c/epsilon² reaches the nonpositive real axis only at purely imaginary
epsilon; its principal logarithm is consequently holomorphic throughout the
right half-plane. The Taylor subtraction at zero and exponential tail bounds
are uniform on its compact subsets. Also E_epsilon(-t)=0 would force
epsilon²=-t/cosh²(sqrt(t)), again purely imaginary epsilon. The spectral cut
and the Jensen/sector estimates above remain valid uniformly on coupling
compacts. Thus the displayed function is jointly meromorphic in s and
holomorphic in the complex coupling, and its zeta determinant remains 4.
The strict positivity in (25) concerns real epsilon>0. Directed numerical
examples in this package use the real couplings one and two.

## 6. Exact relation to the 2024 inverse-function frontier

The coupling (7) is precisely generalized cosine inversion,
epsilon=u sec(u), already contained in Stoutemyer's inverse spherical-Bessel
framework. In the alpha-plane it is the auxiliary deformation
\[
\alpha^2\exp(\varepsilon(\alpha-\alpha^{-1}))=-1,
\qquad u=\varepsilon(\alpha-\alpha^{-1})/(2i).
\]
At epsilon=1 it recovers the original reciprocal parabolic spectrum.
The spectral zeta and boundary operator extend the analytic structure of
that inverse-function family.

Its critical equation is exactly
\[
\frac{d\varepsilon}{du}=\sec u(1+u\tan u)=0.
\]
On u=iv this gives v tanh(v)=1 and the Laplace critical value
epsilon=i v/cosh(v). Thus the earlier inverse-Bessel/Kepler fold is also
the multiple-eigenvalue locus of the characteristic equation (7).
The published branch framework and critical equations are credited to
[Stoutemyer (2024), §§2–4](https://mapletransactions.org/index.php/maple/article/download/16787/16573/55313).
The present boundary/Fredholm realization, trace identities and relative
spectral-zeta formula are derived above.

## Reproducible checks

`computations/verify_cosine_spectrum.py` retains exact trace polynomials,
finite-matrix determinant checks, directed finite-projection error bounds,
phase/parameter recovery checks, canonical-product tails, and directed Mellin
integral evaluations. Working precisions and every numerical scope are recorded
in `computations/cosine-spectrum-results.json`.
