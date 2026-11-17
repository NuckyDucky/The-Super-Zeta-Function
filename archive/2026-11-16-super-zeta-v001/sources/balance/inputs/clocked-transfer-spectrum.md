# Quartet characters, reciprocal transfer operators, and prime-power spectral refinement

16 November 2026. A joint construction with complete proofs and a reproducible
exact/high-precision check.

The four parabolic phases become four character eigenvalues of a single
operator. The certified Dottie inverse branches supply its holomorphic
realization. Prime-power phase covers supply cyclic tensor factors. These
ingredients produce an explicit entire spectral function encoding every
quartet and every retained phase level:

\[
\boxed{
\mathcal Q_p(z;\rho,\eta;s)=
\prod_{n\ge1}\prod_{\sigma,\tau=\pm1}\prod_{k\ge0}
\left[1-
\left(z\rho^n\eta^k
 e^{s(\sigma t_n+i\tau\theta_n)}\right)^{p^k}\right].
}\tag{1}
\]

Here p is prime, |rho|<1 and |eta|<1. The variable s uses the actual retained
logarithms sigma t_n+i tau theta_n. At s=1 its four spectral values are the
actual phases alpha_(n,sigma,tau). The two grading variables retain the
quartet index and the phase-refinement level. For |eta|<1/p, (1) also has the
relative Fredholm construction proved below. A related shifted-phase function
is directly the quotient of two entire Fredholm determinants.

The construction places the existing components inside one precisely defined
spectral object. The geometric inverse maps are evaluated at L_*, the quartet
index enters through exact coefficient weights, and each cyclic factor records
one finite cover of the scalar Fatou clock. These roles remain visible in the
operator and in its product.

## 1. Exact inputs and their domains

The preceding classification gives
\[
\alpha_{n,\sigma,\tau}=e^{\sigma t_n+i\tau\theta_n},\qquad
\cos\theta_n=-t_n/\sinh t_n,
\]
\[
\theta_n+\cosh t_n\sin\theta_n=(2n+1)\pi/2,
\quad t_n>0,\quad \pi/2<\theta_n<\pi,
\quad t_n=\log(2\pi n)+O((\log n)^2/n^2).
\tag{2}
\]
The two commuting sign flips are
\[
r(\alpha)=1/\bar\alpha,
\qquad c(\alpha)=\bar\alpha,
\quad r^2=c^2=1,\quad rc=cr.
\tag{3}
\]
They respectively reverse sigma and tau, generating G=V4. On the parameter
L(alpha)=-e^-alpha/alpha, c sends L to bar L and r sends L to -bar L. Each
n>=1 quartet is a free G-orbit. The two unit Dottie phases form the separate
two-point orbit on which r fixes each phase.

The existing directed inverse certificate is at
\[
L_*=iy_*,\quad y_*=e^{-\sin d},\quad d=\cos d,
\qquad D=\overline B(c_0,8),\quad c_0=-6+19i.
\]
Its two principal-log inverse branches are
\[
b_j(w)=-\frac1{L_*}
\left[\Log\left(\frac{\Log w+2000\pi i}{L_*}\right)+2\pi ij\right],
\qquad j=0,1.
\tag{4}
\]
They are analytic on a neighborhood of D, satisfy g_(L*) b_j=id, have
disjoint images, and obey the convenient strict rational bounds
\[
\sup_D|b'_j|<q:=1/30000,
\qquad \sup_D|b_j-c_0|/8<\varrho:=4/5.
\tag{5}
\]
For the second bound, the retained center displacement plus 8q is less than
8-1.6556<6.4 for both branches. The invariant set K is conjugate to the
one-sided full binary shift by a coding homeomorphism pi.

The normalized p-adic parabolic construction supplies invariant orbit balls
analytically conjugate to Z_p with a->a+1. Its finite reductions have periods
p^k after shifting the precision origin. The scalar Dottie Fatou cylinder
has the same finite phase-cover clocks C_(p^k). These are the clock factors
used here. Frozen proof inputs and their source hashes are in
`sources/dynamics/inputs/` and `local-input-records.json`.

## 2. The actual physical half-step is an exact two-level tower

Set H(w)=exp(iy_* bar w), so H²=g_(L*). A useful simplification occurs in (4):
\[
\boxed{h(w):=H(b_0(w))=H(b_1(w))
 =\overline{\frac{\Log w+2000\pi i}{L_*}}.}\tag{6}
\]
The equality follows by conjugating the logarithm in (4), using bar L*=-L*,
and exponentiating. The extra 2pi i j contributes exp(-2pi i j)=1.
Consequently Hh=id on D and h is injective there. On K,
\[
H=h\circ g,\qquad H(K)=h(K),\qquad Hh=id.
\tag{7}
\]
Indeed every point of K belongs to exactly one b_j(K), and g(K)=K.
The certificate also gives |H(w)|>272.73 for w in D, whereas |w|<28 in D.
Thus K and h(K) are disjoint.

**Physical tower proposition.** On Y=h(K) disjoint-union K, H is conjugate to
\[
\mathcal H(x,0)=(x,1),\qquad
\mathcal H(x,1)=(\sigma x,0).
\tag{8}
\]
The conjugacy is Pi(x,0)=h(pi(x)), Pi(x,1)=pi(x). Equations (7) prove both
intertwining identities, and compactness/injectivity give a homeomorphism.
In particular H|K is two-to-one and H|h(K) is one-to-one. The two levels
retain exactly where the digit is discarded.

For any finite-fixed-point return extension T, the corresponding tower has
\[
\#\operatorname{Fix}(\mathcal H^{2j})=2\#\operatorname{Fix}(T^j),
\qquad \#\operatorname{Fix}(\mathcal H^{2j+1})=0,
\qquad \zeta_{\mathcal H}(z)=\zeta_T(z^2).
\tag{9}
\]
This follows directly from the two levels and the definition
zeta_T(z)=exp(sum_(j>=1) #Fix(T^j) z^j/j). The actual unextended repeller
therefore has zeta_H(z)=1/(1-2z²).

## 3. A finite quartet-and-clock extension with exact character factors

Mark symbol 0 by r and symbol 1 by c in G. This choice is part of the
constructed extension. On X={0,1}^N, let
\[
T_m(x,a,g)=(\sigma x,a+1,g+e_{x_0}),
\qquad a\in C_m,\quad g\in G,\quad e_0=r,e_1=c.
\tag{10}
\]
The second coordinate is the actual finite phase-clock model. The third
retains the cumulative quartet sign action of the marked word. Give each
symbol the complex weight u or v. Closed weighted walks on C_m x G have
adjacency operator A=R_m tensor (u R_r+v R_c), where all R are permutation
operators. Fourier transformation on G diagonalizes the second factor:
\[
\lambda_{\sigma,\tau}=\sigma u+\tau v.
\]
The roots of unity diagonalize R_m. Hence
\[
\boxed{\zeta_{m,G}(z;u,v)=
\prod_{\sigma,\tau=\pm1}
\left[1-(z(\sigma u+\tau v))^m\right]^{-1}.}\tag{11}
\]
Equivalently, its weighted fixed-point sum at time j is zero unless m divides
j, and otherwise is m sum_(sigma,tau)(sigma u+tau v)^j. To prove this by
words, sum the accumulated G-element in the regular representation: its
trace is four for the identity and zero for each other group element. The
character sum is the same identity test. Thus (11) is both a finite matrix
determinant and the weighted periodic-orbit zeta of (10).

The unweighted case u=v=1 is especially explicit:
\[
\zeta_{m,G}(z;1,1)=
\begin{cases}
(1-(2z)^{2m})^{-1},&m\text{ odd},\\
(1-(2z)^m)^{-2},&m\text{ even}.
\end{cases}\tag{12}
\]
The physical extension uses z² in (11)-(12). This retains the physical
half-step separately from the independently marked sign cocycle.

## 4. The holomorphic operators retain the actual reciprocal inverse maps

Let H²(D) be the Hardy Hilbert space on the interior of D, with orthonormal
basis e_l(w)=((w-c_0)/8)^l. For j=0,1 define
\[
C_{0,j}f=f\circ b_j,
\qquad C_{1,j}f=b'_j(f\circ b_j).
\]
For epsilon=0,1 and complex weights u,v put
\[
\mathcal L_{\epsilon}(u,v)=uC_{\epsilon,0}+vC_{\epsilon,1}.
\tag{13}
\]
These are trace-class operators. In fact (5) gives the rank-one expansion
C_(0,j)=sum_l (C_(0,j)e_l) tensor e_l*, with
||C_(0,j)e_l||<=varrho^l. Multiplication by b'_j gives the analogous
epsilon=1 bound. Thus
\[
\boxed{\|\mathcal L_0(u,v)\|_1\le5(|u|+|v|),\qquad
\|\mathcal L_1(u,v)\|_1\le5q(|u|+|v|).}\tag{14}
\]

**Trace and determinant proposition.** For every j>=1,
\[
\operatorname{tr}(\mathcal L_0(u,v)^j)
-\operatorname{tr}(\mathcal L_1(u,v)^j)=(u+v)^j.
\tag{15}
\]
Consequently their entire Fredholm determinants satisfy
\[
\boxed{\det(I-z\mathcal L_0(u,v))
 =[1-z(u+v)]\det(I-z\mathcal L_1(u,v)).}\tag{16}
\]

**Proof.** An inverse word B has one fixed point w_B, contraction derivative
|B'(w_B)|<=q^j, and weight W_B. In a normalized unit coordinate, the trace
of the weighted composition h(f composed with B) is
\[
\sum_{l\ge0}\frac1{2\pi i}\int_{|\xi|=1}
 \frac{h(\xi)B(\xi)^l}{\xi^{l+1}}d\xi
=\frac1{2\pi i}\int\frac{h(\xi)}{\xi-B(\xi)}d\xi
=\frac{h(w_B)}{1-B'(w_B)}.
\]
Uniform contraction makes the geometric series exchange valid; the unique
fixed point gives the residue. Applying the formula to the two word
operators gives W_B/(1-B') and W_B B'/(1-B'). Their difference is W_B.
Summing all words gives (u+v)^j and proves (15). The trace expansion of log
det near zero gives (16), and entire continuation gives the identity for
all z. This is a self-contained one-dimensional specialization of Ruelle's
holomorphic trace/determinant construction. ∎

Tensoring (13) with R_m gives the finite-clock version
\[
\det(I-z\mathcal L_0\otimes R_m)
 =[1-(z(u+v))^m]\det(I-z\mathcal L_1\otimes R_m).
\tag{17}
\]
Indeed trace(R_m^j)=m if m divides j and zero otherwise. Choosing weights
u=sigma u_0, v=tau v_0 and multiplying the four identities recovers (11)
from the actual inverse-branch operators. Their individual determinants
retain the derivatives and positions of the inverse maps; their quotient
has the exact spectral cancellation in (15).

## 5. The quartet phases emerge by exponential functional calculus

For quartet n choose u_0=t_n and v_0=i theta_n. In the four character
sectors,
\[
\lambda_{n,\sigma,\tau}=\sigma t_n+i\tau\theta_n,
\qquad e^{\lambda_{n,\sigma,\tau}}=\alpha_{n,\sigma,\tau}.
\tag{18}
\]
At the finite group-matrix level this is the particularly simple identity
\[
X_n=t_n R_r+i\theta_n R_c,
\qquad e^{X_n}=e^{t_nR_r}e^{i\theta_nR_c},
\]
whose four eigenvalues are exactly the quartet. The same statement survives
in the holomorphic realization through (15).

**Functional-calculus corollary.** If phi is entire and phi(0)=0, then
\[
\det(I-z\phi(\mathcal L_0))
 =[1-z\phi(u+v)]\det(I-z\phi(\mathcal L_1)).
\tag{19}
\]
To prove it, expand phi(w)^j in its entire series, which has zero constant
term. The trace-class series converges absolutely on each bounded operator
ball. Applying (15) term by term gives
tr(phi(L0)^j)-tr(phi(L1)^j)=phi(u+v)^j. The determinant proof of (16)
then applies. In particular
\[
A_{\epsilon,n,\sigma,\tau}(s)
=e^{s\mathcal L_\epsilon(\sigma t_n,i\tau\theta_n)}-I
\tag{20}
\]
is trace class and its determinant quotient has the sole extra eigenvalue
alpha_(n,sigma,tau)^s-1, with the logarithmic lift in (18).

For m=1, (19) gives the quartet polynomial after the affine spectral change
x=1+1/z. Thus the exact original quartet phases, including their ordered
logarithms, have entered the reciprocal inverse transfer spectrum.

## 6. One infinite Fredholm construction for all quartets and all clock levels

For |rho|<1 and |eta|<1/p define on the Hilbert direct sum over
(n,sigma,tau,k) the trace-class operators
\[
\mathcal B_\epsilon(s)
=\bigoplus_{n,\sigma,\tau,k}
\rho^n\eta^k A_{\epsilon,n,\sigma,\tau}(s)\otimes R_{p^k}.
\tag{21}
\]
For every compact s-set, (14), (2), and
||e^(sL)-I||_1<=|s| ||L||_1 exp(|s| ||L||) show that the A-block norms
grow at most polynomially in n, times log(n+1). The rho^n sum converges.
The tensor factor multiplies trace norm by p^k, so the level sum is
sum_k(p|eta|)^k. This proves trace-class convergence, locally uniformly.

The **direct entire determinant identity** is
\[
\boxed{\frac{\det(I-z\mathcal B_0(s))}
{\det(I-z\mathcal B_1(s))}
=\prod_{n,\sigma,\tau,k}
\left[1-
\left(z\rho^n\eta^k
(e^{s\lambda_{n,\sigma,\tau}}-1)\right)^{p^k}\right].}\tag{22}
\]
At common zeros the right side supplies the analytic extension of the
quotient. This is the shifted-phase version of (1). It is an actual
Fredholm realization of the whole infinite family, with the geometric
IFS, quartet representation, and phase clock retained in each block.

For the unshifted phases in (1), put a=rho^n eta^k, m=p^k and
E_epsilon=exp(s L_epsilon). Away from (za)^m=1 define the relative block
determinant
\[
\mathcal R_\epsilon(z;a,m)
=\det\left(I-
za[(E_\epsilon-I)\otimes R_m]
[I-za(I\otimes R_m)]^{-1}\right).
\tag{23}
\]
It compares I-za E_epsilon tensor R_m with the common background
I-za I tensor R_m. Diagonalizing R_m and using (19) gives exactly
\[
\boxed{\frac{\mathcal R_0}{\mathcal R_1}
=\frac{1-(za e^{s\lambda})^m}{1-(za)^m}.}\tag{24}
\]
Multiplying (24) by the finite background factor 1-(za)^m recovers the
corresponding factor of (1). The direct sum of the perturbations in (23)
is trace class by the same bound as (21), locally away from the background
spectral set. Multiplying all background factors and all relative quotients
therefore gives (1) as a relative Fredholm spectral function. Formula (1)
supplies its continuation across the canceled background locations.

For nonzero rho and eta, the spectrum has a simple explicit description:
zeros of (1) occur at
\[
z=\rho^{-n}\eta^{-k}e^{-s\lambda_{n,\sigma,\tau}}\omega,
\qquad \omega^{p^k}=1,
\tag{25}
\]
with multiplicities added at coincidences. Thus phase refinement multiplies
each marked quartet spectral value by all p^k-th roots of unity, while the
two grades keep its origin recoverable.

## 7. Entire continuation and an exact prime-refinement equation

**Joint spectral theorem.** The product (1) converges normally on compact
subsets of z,s in C, |rho|<1, |eta|<1, and defines a jointly holomorphic
function there. It is entire in z and s. If
\[
\mathcal A(z;\rho;s)
=\prod_{n\ge1,\sigma,\tau}
[1-z\rho^n e^{s\lambda_{n,\sigma,\tau}}],
\]
then
\[
\boxed{
\mathcal Q_p(z;\rho,\eta;s)
=\mathcal A(z;\rho;s)
\mathcal Q_p((z\eta)^p;\rho^p,\eta^p;ps).
}\tag{26}
\]

**Proof.** On a compact s-set, (2) implies
|exp(s lambda_n)|<=C(n+1)^M uniformly in the four signs. Therefore
M_n=|rho|^n C(n+1)^M is summable. On any compact parameter set with
|rho|,|eta| bounded below one, eventually |z|M_n|eta|^k<1/2. For those
terms, raising to p^k decreases the absolute value; summability follows
from sum_n M_n sum_k |eta|^k. The remaining finite terms cause no
convergence issue. Standard normal convergence of products proves the
holomorphic statement. Splitting off k=0 and relabeling k+1 gives (26)
term by term. ∎

### A controlled truncation of the entire joint spectrum

There is a convenient explicit global bound
\[
\boxed{|\alpha_{n,\sigma,\tau}|<4\pi n.}\tag{27a}
\]
For t_n<2 this follows from e²<4pi. For t_n>=2, the function t/sinh(t)
decreases and 2/sinh(2)<3/5. Hence sin(theta_n)>4/5, and (2) gives
e^(t_n)<2 cosh(t_n)<(5pi/2)(n+1/2)<=4pi n. The reciprocal-radius phases
satisfy the same bound.

At s=1, choose |z|<=Z, |rho|<=r<1, |eta|<=h<1 and truncate to
1<=n<=N, 0<=k<=K. Put C=4pi, x_n=C Z n r^n, and choose N so x_n is
decreasing after N and x_(N+1)<1. Write
\[
A=\max_{1\le n\le N}x_n,\quad
b=Ah^{K+1}<1,\quad P=p^{K+1},\quad B=b^P,
\]
\[
S=\frac{4CZr^{N+1}[(N+1)-Nr]}{(1-r)^2(1-h)}
 +\frac{4NB}{1-h^P},
\qquad \delta=\max(x_{N+1},B)<1.
\tag{27b}
\]
Then the omitted factor R=Q_full/Q_partial satisfies
\[
\boxed{|R-1|\le\exp\left(\frac{S}{1-\delta}\right)-1.}\tag{27c}
\]
To prove it, the omitted n>N terms are bounded by x_n h^k, whose sum is
the first term in S. For n<=N and k>K, their sum is at most
4N b^P/(1-h^P), giving the second term. Every omitted monomial has
modulus at most delta. The inequality |log(1-u)|<=|u|/(1-delta) now
bounds the logarithm of the remaining product, proving (27c).

The script evaluates the full actual-phase product at p=2, z=1/20,
rho=3/10, eta=1/10, N=32, K=3. It replaces C by the rational upper
bound 88/7 and evaluates S and delta using exact Fractions. For the
resulting S/(1-delta)<1/2, the simpler rigorous bound
|R-1|<=2S/(1-delta) is retained as an exact rational in the results file.
The partial product itself is evaluated at 130 decimal digits. The same
program checks (26) with complex s=0.7+0.2i for p=2,3,5.

Equation (26) is a Mahler-type refinement identity with an explicit action
on both the phase power and the grading variables. It follows from the
actual prime-power cover tower. The reciprocal of (1) is the associated
joint weighted spectral zeta. The physical two-level extension evaluates
the return variable at z², preserving (9).

## 8. The inverse limit and the retained-level spectrum give different exact zetas

For the binary shift times a single clock C_m, the ordinary unweighted
fixed-point count and zeta are
\[
N_j=m2^j\mathbf1_{m\mid j},\qquad
\zeta_m(z)=[1-(2z)^m]^{-1}.
\tag{27}
\]
The inverse limit is the actual product of the shift with the adding machine
on Z_p. Its clock equation a+j=a has no solution for any positive integer
j, so its fixed-point counts are zero and its ordinary zeta equals 1.
Its finite-cover zetas converge locally uniformly to 1 on |z|<1/2.

Retaining every finite level as a graded disjoint union instead gives
\[
\mathcal H_p(x)=\prod_{k\ge0}(1-x^{p^k})^{-1},
\qquad x=2z,
\quad \mathcal H_p(x)=\frac{\mathcal H_p(x^p)}{1-x}.
\tag{28}
\]
Every positive time still has finitely many fixed points in this union:
\[
N_j=2^j\sum_{k=0}^{v_p(j)}p^k
=2^j\frac{p^{v_p(j)+1}-1}{p-1}.
\tag{29}
\]
Consequently (28) is its exact Artin–Mazur zeta. It records the prime
valuation of each iteration time. The p-adic information is explicit in
the coefficient sequence.

For completeness, (28) has the unit circle as a natural boundary in x.
At any root of unity of p-power order p^a, take x=r omega with r increasing
to one. The finitely many factors k<a approach finite nonzero limits.
The remaining factors are positive (1-r^(p^k))^-1, and their product tends
to infinity. Such roots are dense on the unit circle. Analytic continuation
across any boundary arc would encounter one of these singular points.
The reciprocal product tends to zero faster than every fixed power of
1-r there, which also gives the corresponding obstruction to a meromorphic
extension. The grading eta in (1) moves this boundary accumulation into a
normally convergent entire spectral product.

The principal p-adic exponential fixed-pair map has a different exact
ordinary zeta, (1-z)^-1: its unique fixed pair is its sole periodic point.
The parabolic p-adic orbit balls carry the adding-machine zeta 1; their
finite clocks and graded levels are given by (27)-(29), with the binary
factor omitted when only the clock is retained. Each formula follows the
specified map and state space.

## 9. Source comparison, computation, and further calculations

Artin–Mazur's 1965 paper supplies the fixed-point exponential definition of
the dynamical zeta. Ruelle's 1976 Theorem 1 and holomorphic trace lemma
supply the published Fredholm framework; Sections 4-6 give its direct
Hardy-space proof for the reciprocal branches. Boyle–Schmieding, 2016,
Section 2 and its introduction formulate finite group shift extensions by
group-ring matrices and retain group-valued periodic data. The exact marked
G=V4 extension, its log-phase weights, exponential functional calculus,
infinite two-grade product, and refinement identity are developed here.

Primary texts, retained in `sources/dynamics/`, are:

- [Artin–Mazur, On periodic points (1965)](https://pdodds.w3.uvm.edu/files/papers/others/everything/artin1965a.pdf).
- [Ruelle, Zeta-functions for expanding maps and Anosov flows (1976)](https://www.ihes.fr/~ruelle/PUBLICATIONS/%5B45%5D.pdf).
- [Boyle–Schmieding, Finite group extensions of shifts of finite type (2016 version)](https://arxiv.org/pdf/1503.02050).

Run `computations/verify_clocked_transfer.py` with Python and mpmath. The
record is `computations/clocked-transfer-results.json`. It contains:

- Exact weighted closed-walk traces for m=1,2,3,4,5,8,9, through the full
  matrix dimension 4m; Newton reconstruction of each determinant matches
  the independently multiplied four character factors.
- Direct walks on the doubled physical graph, verifying (9).
- Exact integer series through degree 96 for primes 2,3,5,7, verifying
  the Mahler equation and the prime-valuation fixed-point formula.
- 130-decimal-digit computations of all 126 inverse words of lengths
  1 through 6, their composition fixed points and derivatives, checking
  (15) on the actual complex Dottie branches.
- Explicit physical identities H b_0=H b_1=h and Hh=id at three disk
  points; errors below 10^-120.
- Six independently solved quartet levels, the 4x4 matrix exponential
  eigenvalue identity, and successive small graded-product truncations.
- Thirty-two quartet levels in the full joint product, three prime
  renormalization checks at complex s, and an exact rational relative
  truncation bound for the infinite actual-phase product.

The exact algebraic proofs supply the infinite statements. The 130-digit
trace and matrix-exponential results are numerical checks with their actual
residuals recorded. The disk/contraction bounds are inherited from the frozen
768-bit directed inverse certificate. The results file records the full
CPU runtime, numerical residuals, and the explicit infinite-product bound.

The next geometric calculation is to register a selected cap orbit and its
inverse word on a specific parameter continuation, then retain its sign
cocycle and clock sheet along that path. That record can replace the marked
choice in (10) with the computed continuation action. The operator framework
already accepts a general finite-state transition matrix or group-valued
cocycle. Derivative-dependent weights can then retain the local geometry in
the periodic trace instead of taking the alternating cancellation (15).
These give concrete routes from the joint spectral construction to the
registered cap/horn data.
