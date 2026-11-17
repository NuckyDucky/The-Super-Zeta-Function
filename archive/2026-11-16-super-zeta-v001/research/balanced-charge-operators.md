# Balanced histories are a charge projection of the reciprocal transfer spectrum

16 November 2026. Exact operator construction, a new directed four-branch
Dottie certificate, prime-clock filters, and a controlled multivariate product.

The current quartet determinant has a natural continuous character extension.
Its four sign characters become the four points of a two-torus with coordinates
xi,upsilon in {+1,-1}. Averaging over the whole torus selects histories whose
two integer charges return to zero. At the isotropic normalization, the exact
return probabilities are B_j², where B_j=binom(2j,j)/4^j. At an actual quartet,
the same projection is the explicit Bessel kernel I_0(st_n)J_0(s theta_n).

The construction uses actual holomorphic inverse branches of the reciprocal
map. It preserves each ordered inverse word in its individual operators;
the trace difference has a closed lattice expression. Cyclic clock factors
then select prime-power return times. This connects the balanced probabilities
to the existing quartet Q_p through a specified operator and a specified trace.

Throughout, K(m) denotes the elliptic integral in the **parameter** convention
\[
K(m)=\int_0^{\pi/2}(1-m\sin^2\phi)^{-1/2}\,d\phi.
\]

## 1. From the four signs to integer charges

Let S_1,S_2 be the bilateral coordinate shifts on ell²(Z²). Their reduction
modulo two gives the two V4 generators r,c. The symmetric lifts are
\[
C_1=(S_1+S_1^{-1})/2,\qquad C_2=(S_2+S_2^{-1})/2.
\]
For complex a,b define
\[
X(a,b)=aC_1+bC_2.
\tag{1}
\]
Fourier transformation identifies these shifts with multiplication by xi and
upsilon on T². Thus the symbol is
\[
X(a,b;\xi,\upsilon)
=\frac a2(\xi+\xi^{-1})+\frac b2(\upsilon+\upsilon^{-1})
=a\cos\phi+b\cos\psi.
\tag{2}
\]
At xi=sigma and upsilon=tau, with sigma,tau=+/-1, this is sigma a+tau b.
For the nth actual quartet choose
\[
a=t_n,\qquad b=i\theta_n.
\]
The four evaluations are exactly the retained logarithms
\[
\lambda_{n,\sigma,\tau}=\sigma t_n+i\tau\theta_n,
\qquad e^{s\lambda_{n,\sigma,\tau}}
=\alpha_{n,\sigma,\tau}^{\,s},
\tag{3}
\]
where the power uses this displayed logarithm. Splitting each generator into
its two inverse integer directions is the symmetric lift of the earlier
V4 group-matrix construction.

The canonical lattice trace is
\[
\tau(A)=\langle A\delta_0,\delta_0\rangle
=\operatorname{CT}_{\xi,\upsilon}A
=\frac1{(2\pi)^2}\int_{T^2}A\,d\phi\,d\psi.
\tag{4}
\]
It selects zero displacement in Z². The four steps are +e_1,-e_1,+e_2,-e_2.
A pair of independent signs (epsilon_1,epsilon_2) maps bijectively to these
steps by ((epsilon_1+epsilon_2)/2,(epsilon_1-epsilon_2)/2). A length-2j
walk returns to zero precisely when both sign streams balance. Therefore
\[
\boxed{\tau\left[X(1/2,1/2)^{2j}\right]
=\frac{\binom{2j}{j}^2}{16^j}=B_j^2,\qquad
\tau\left[X(1/2,1/2)^{2j+1}\right]=0.}
\tag{5}
\]
This is the exact probability normalization for the four equiprobable steps.

More generally the moments are finite polynomials:
\[
\boxed{M_{2j}(a,b):=\tau(X^{2j})
=\frac{(2j)!}{4^j}\sum_{h=0}^j
\frac{a^{2h}b^{2j-2h}}{h!^2(j-h)!^2},\qquad M_{2j+1}=0.}
\tag{6}
\]
Choose h positive and h negative first-coordinate steps and j-h of each
second-coordinate step. The multinomial count and weights a/2,b/2 prove (6).

## 2. The anisotropic lattice kernel is elliptic, and its heat kernel is Bessel

For |z|(|a|+|b|)<1, the lattice resolvent is
\[
G(z;a,b)=\tau[(I-zX)^{-1}]=\sum_{j\ge0}M_j(a,b)z^j.
\]
It has the exact elliptic form
\[
\boxed{G(z;a,b)=\frac{2}{\pi\sqrt{1-z^2(a-b)^2}}
K\!\left(\frac{4abz^2}{1-z^2(a-b)^2}\right).}
\tag{7}
\]
All branches here are their analytic germs at z=0. This convention also covers
complex a,b, including b=i theta_n.

**Proof.** The degree-two torus map (u,v)->(u+v,u-v) preserves normalized
Haar measure. Its transformed symbol is
(a+b)cos(u)cos(v)+(b-a)sin(u)sin(v). Integrating first in v gives
\[
[1-z^2((a+b)^2\cos^2u+(a-b)^2\sin^2u)]^{-1/2}.
\]
For real parameters near zero this is the elementary average of the
resolvent of A cos(v)+B sin(v). Its power series gives the identity for
complex parameters as well. Factoring 1-z²(a-b)² in the remaining u
integral gives (7). ∎

The entire heat trace factorizes:
\[
\boxed{\tau(e^{sX(a,b)})=I_0(sa)I_0(sb).}
\tag{8}
\]
Expand the two commuting exponential factors and take their two independent
constant terms, or integrate each angle. At the actual quartet this is
\[
\boxed{\tau(e^{sX_n})=I_0(st_n)J_0(s\theta_n).}
\tag{9}
\]
The classical I_0 integral is [DLMF 10.32.1](https://dlmf.nist.gov/10.32.E1).
The isotropic specialization of (7) is G(z;1/2,1/2)=2K(z²)/pi, the square
lattice Green function. Its probability and constant-term setting is treated
by [Guttmann (2010), equations (1)-(6)](https://arxiv.org/pdf/1004.1435).

The shifted-superzeta theorem in [the companion note](shifted-superzeta.md)
gives Res_(s=1/2-j) S(s,w;epsilon)=B_j w^j/pi. Consequently, for w!=0,
\[
\boxed{\left[\frac\pi{w^j}
\operatorname*{Res}_{s=1/2-j}\mathscr S(s,w;\varepsilon)\right]^2
=\tau[X(1/2,1/2)^{2j}].}
\tag{10}
\]
The spectral residue order j and the walk half-length j enter this identity
through their explicit shared coefficient. The quartet label n remains the
independent parameter index in (3).

## 3. A new actual four-branch Dottie repeller

Let d=cos d, y_*=exp(-sin d), L_*=iy_*, and
\[
\boxed{D=\overline B(-37/2+32i,20),\qquad k=10^6.}
\]
On D take principal logarithms and define four inverse branches
\[
b_j(w)=-\frac1{L_*}
\left[\Log\left(\frac{\Log w+2\pi ik}{L_*}\right)+2\pi ij\right],
\quad j=0,1,2,3.
\tag{11}
\]
The disk is in Im(w)>=12 and avoids zero. The inner quotient has positive
real part, so both displayed logarithms are analytic on a neighborhood of D.
The directed certificate in `balanced-charge-results.json` gives

| Quantity | Proved bound |
|---|---|
| Uniform inverse derivative | <1/50,000,000; evaluated bound 1.84021507196... x 10^-8 |
| Minimum invariance margin | >1.49998 |
| Image separation | >12.32326 |
| Maximum image distance from the disk center | <19, hence relative radius <19/20 |
| Modulus of the physical image H(D) | >454.12, while |w|<57 on D |

For completeness the analytic derivative bound is
\[
q\le\frac1{y_*(|c|-20)
[2\pi k-(\log(|c|+20)+\pi)]},\qquad c=-37/2+32i.
\tag{12}
\]
The strict center inequalities |b_j(c)-c|+20q<20 prove invariance, and
2pi/y_*-40q>12.32326 proves separation. Nested inverse disks therefore
give a compact repeller K_4 conjugate to the full four-symbol shift.

These are actual inverses of g_(L*), with the displayed sheets retained.
Assign j=0,1,2,3 the charges +e_1,-e_1,+e_2,-e_2 respectively.

## 4. The balanced coefficients are actual holomorphic supertraces

On the Hardy space H²(D) let
\[
C_{0,j}f=f\circ b_j,\qquad
C_{1,j}f=b'_j(f\circ b_j).
\]
The image fraction 19/20 gives trace norm bounds
||C_(0,j)||_1<=20 and ||C_(1,j)||_1<=20q by expanding in the normalized
monomial basis. For xi,upsilon on T² define the trace-class operators
\[
\begin{aligned}
\mathcal L_\epsilon(a,b;\xi,\upsilon)={}&
\frac a2[\xi C_{\epsilon,0}+\xi^{-1}C_{\epsilon,1}]\\
&+\frac b2[\upsilon C_{\epsilon,2}
                   +\upsilon^{-1}C_{\epsilon,3}],\quad\epsilon=0,1.
\end{aligned}\tag{13}
\]
Their trace norms are at most 20(|a|+|b|), and 20q(|a|+|b|), respectively.
Equivalently these are the Fourier fibers of a charge-translation operator on
H²(D) tensor ell²(Z²). Its trace per charge cell is
\[
\mathfrak T(A)=\int_{T^2}\operatorname{tr}_{H^2(D)}A(\xi,\upsilon)\,d\mu.
\tag{14}
\]
It is the ordinary holomorphic trace combined with the canonical lattice
trace (4). The finite trace norm integral supplies its domain here.

**Charge-supertrace theorem.** For every integer m>=1,
\[
\boxed{\operatorname{tr}(\mathcal L_0^m)
-\operatorname{tr}(\mathcal L_1^m)
=X(a,b;\xi,\upsilon)^m,}
\tag{15}
\]
\[
\boxed{\mathfrak T(\mathcal L_0^m)-\mathfrak T(\mathcal L_1^m)
=M_m(a,b).}
\tag{16}
\]

**Proof.** Each ordered inverse word B has one fixed point w_B and derivative
|B'(w_B)|<=q^m. The Cauchy/residue formula gives its function trace as
1/(1-B'(w_B)), and its derivative-weighted trace as B'(w_B)/(1-B'(w_B)).
Their difference is one. Multiply by the actual ordered word's coefficient
and its Laurent charge monomial, then sum all four-letter words. The result
is exactly the mth power of (2), proving (15). Taking the constant term
proves (16). Trace-class convergence permits every finite-word sum and
Fourier integral. This is the one-dimensional holomorphic trace mechanism
of Ruelle, specialized here to the certified branches and the retained
integer charges. ∎

In particular the normalized isotropic case gives
\[
\boxed{\mathfrak T(\mathcal L_0^{2j})
-\mathfrak T(\mathcal L_1^{2j})=B_j^2.}
\tag{17}
\]
The two individual traces retain the fixed points, multipliers and order of
the selected words. Their difference is the exact balanced return coefficient.
At a quartet, their exponential-functional-calculus difference is (9).

Define the analytic trace determinant as the germ
\[
\operatorname{Det}_{\mathfrak T}(I-zA)
=\exp\left[-\sum_{m\ge1}\frac{z^m}{m}\mathfrak T(A^m)\right].
\tag{18}
\]
The series converges when |z| ||A||<1. Thus the supertrace ratio is the exact
lattice determinant
\[
\frac{\operatorname{Det}_{\mathfrak T}(I-z\mathcal L_0)}
{\operatorname{Det}_{\mathfrak T}(I-z\mathcal L_1)}
=\exp\left[-\sum_{m\ge1}\frac{M_m(a,b)z^m}{m}\right].
\tag{19}
\]
This specifies both the trace and the analytic branch. For the positive
isotropic lattice operator and real |z|<1 it agrees with the positive
trace determinant. Analytic trace determinants in periodic-graph settings
are developed by [Guido–Isola–Lapidus (2006), §5](https://preprints.ihes.fr/storage/LapidusM39.pdf).
The individual fiber determinants in (13) are ordinary Hardy-space Fredholm
determinants; (18) integrates their logarithms per charge cell.

## 5. Prime clocks filter the balanced histories exactly

Tensor with the cyclic permutation R_m on C_m and use the ordinary finite
matrix trace on this factor. Since tr(R_m^j)=m times the indicator m|j,
\[
\boxed{\mathfrak T_m[(\mathcal L_0\otimes R_m)^j]
-\mathfrak T_m[(\mathcal L_1\otimes R_m)^j]
=m\mathbf1_{m\mid j}M_j(a,b).}
\tag{20}
\]
The corresponding inverse determinant satisfies the exact root filter
\[
\zeta_{{\rm bal},m}(z;a,b)
=\prod_{\omega^m=1}\zeta_{{\rm bal},1}(\omega z;a,b).
\tag{21}
\]
At a=b=1/2 the unclocked logarithm is
\[
\log\zeta_{{\rm bal},1}(z)
=\sum_{j\ge1}\frac{B_j^2z^{2j}}{2j}.
\tag{22}
\]
The factor 2j is the full walk length. The scalar/critical-value treatment
and primitive balanced histories are developed in
[the ordered-history note](ordered-signed-histories.md); (20)-(22) give
the actual holomorphic operator realization and clock.

Retaining all finite prime clocks, with level weight eta^k, gives
\[
\mathcal Z_{p,{\rm bal}}(z;\eta)
=\prod_{k\ge0}\zeta_{{\rm bal},p^k}(\eta^kz).
\tag{23}
\]
At eta=1 and |z|<1 this converges normally. The coefficient at an even
time j=2h in z d(log Z)/dz is exactly
\[
\boxed{B_h^2\sum_{k=0}^{v_p(2h)}p^k
=B_h^2\frac{p^{v_p(2h)+1}-1}{p-1}.}
\tag{24}
\]
The odd coefficients vanish. Convergence follows from M_j<=1 and
sum_k[-log(1-|z|^(p^k))]<infinity. For the completed p-adic clock itself,
positive integer translation has no fixed point; its finite-cover trace
filters tend to zero at every fixed positive time. These are the specified finite
clock, retained-level and inverse-limit observables.

## 6. An exact charge extension of the existing quartet Q_p

Set X_n(ξ,upsilon)=X(t_n,i theta_n;ξ,upsilon). Define
\[
\widehat{\mathcal Q}_p(z;\rho,\eta;s;\xi,\upsilon)
=\prod_{n\ge1,k\ge0}
\left[1-\left(z\rho^n\eta^k e^{sX_n(\xi,\upsilon)}\right)^{p^k}\right].
\tag{25}
\]
For |rho|<1, |eta|<1 it converges normally on compact z,s and compact
subsets of (C*)² in the two character variables. Indeed t_n=O(log n),
theta_n<pi, so the exponential weights grow polynomially in n on those
compacts, while rho^n supplies summability. It is entire in z,s and
holomorphic in the two nonzero character variables.

The earlier quartet product is recovered exactly by the four sign characters:
\[
\boxed{\mathcal Q_p(z;\rho,\eta;s)
=\prod_{\sigma,\tau=\pm1}
\widehat{\mathcal Q}_p(z;\rho,\eta;s;\sigma,\tau).}
\tag{26}
\]
This is the same full sequence of phases and prime clocks as before, now
with its continuous charge variables retained.

The zero-charge counterpart averages its logarithm. On the germ with value
one at z=0, put
\[
\mathcal Q_{p,0}
=\exp\left[\operatorname{CT}_{\xi,\upsilon}
\log\widehat{\mathcal Q}_p\right].
\tag{27}
\]
By (9) it has the explicit convergent Bessel formula
\[
\boxed{\log\mathcal Q_{p,0}(z;\rho,\eta;s)
=-\sum_{n\ge1,k\ge0,l\ge1}
\frac{(z\rho^n\eta^k)^{p^kl}}{l}
I_0(sp^klt_n)J_0(sp^kl\theta_n).}
\tag{28}
\]
A sufficient domain is
\[
|\eta|\le1,\qquad
|z|\sup_{n\ge1}|\rho|^n e^{|s|(t_n+\theta_n)}<1.
\tag{29}
\]
This gives a nonempty analytic z-germ, jointly holomorphic on each strict
domain of this form. Its trace definition averages log(Qhat), as specified
in (27).

To obtain its operator realization, use (13) with a=t_n,b=i theta_n in
each Bloch fiber. Identity (15) extends to every entire functional calculus
phi with phi(0)=0 by expansion in trace-class power series. Therefore the
operators exp(s L_epsilon)-I have the trace difference exp(sX_n)-1.
The relative Fredholm ratio, with scalar background I, at phase length m is
\[
\frac{1-(z\rho^n\eta^k e^{sX_n})^m}
{1-(z\rho^n\eta^k)^m}.
\]
Restoring the displayed background factor, integrating its logarithm, and
taking the prime-clock and quartet grades gives exactly (28). For
|eta|<1/p the graded perturbations are trace class per charge cell: the
clock norm sum is sum_k(p|eta|)^k, while the quartet norm grows at most
polynomially and is controlled by rho^n. Formula (28) gives the stated
germ also at the retained-level boundary eta=1 under (29).

Splitting off k=0 gives the refinement identity
\[
\boxed{\mathcal Q_{p,0}(z;\rho,\eta;s)
=\mathcal A_0(z;\rho;s)
\mathcal Q_{p,0}((z\eta)^p;\rho^p,\eta^p;ps),}
\tag{30}
\]
where log(A_0) is the k=0 Bessel sum. Every logarithm uses the germ at z=0.

## 7. A rigorous complete-product approximation

At |s|<=1 the established bound exp(t_n)<4pi n and theta_n<pi imply
exp(|s|(t_n+theta_n))<320n. Take
\[
p=2,\quad z=1/1000,\quad\rho=\eta=1/4,\quad s=1.
\]
Then r_n=320|z|n|rho|^n<=A=2/25. Truncate (28) to n<=N,k<=K,l<=J.
The absolute omitted logarithm is at most
\[
\boxed{E_{N,K,J}\le
\frac{320|z|\,r^{N+1}[(N+1)-Nr]}{(1-r)^2(1-A)^2}
+\frac{NA^{p^{K+1}}}{(1-A)^2}
+\frac{N(K+1)A^{J+1}}{(J+1)(1-A)},\qquad r=1/4.}
\tag{31}
\]
For the first term use p^k>=k+1 and sum all clock levels of each omitted
n by r_n/(1-r_n)². For omitted levels of retained n, sum from k=K+1 by
A^(p^(K+1))/(1-A)². The remaining l-tail is its geometric logarithmic
tail, giving the last term. The Bessel integrals (8) are bounded by the
exponential majorants used in r_n, so all three estimates apply to (28).

The script uses N=64,K=4,J=40. Terms smaller than a fixed exact rational
threshold are replaced by an additional proved geometric tail bound.
The complete omitted-product relative error is at most exp(E)-1<=2E.
All bound arithmetic is exact Fractions. At 130 decimal digits it evaluates
1063 retained Bessel terms and obtains
\[
\boxed{\mathcal Q_{2,0}(10^{-3};1/4,1/4;1)
\approx0.9998702455821832515935638266904876236883,}
\]
with relative omitted-product bound
\[
\boxed{<1.198206\times10^{-33}.}
\tag{32}
\]
The Bessel partial sum is a high-precision point computation. The quoted
omitted-product estimate is an exact analytic/rational bound and is recorded
as an exact fraction in `balanced-charge-results.json`.

## 8. Physical steps and reproducible scope

For H(w)=exp(iy_*bar(w)), the four branches in (11) satisfy
\[
Hb_j=h\quad(j=0,1,2,3),\qquad
h(w)=\overline{(\Log w+2\pi ik)/L_*},\qquad Hh=id.
\]
The certificate separates H(K_4) from K_4. Consequently H is the exact
two-level tower (x,0)->(x,1), (x,1)->(shift(x),0), with the charge and
finite-clock update at the scalar-return completion. Physical trace zetas
and determinants use z² in their scalar-return variable. A balanced word
of length 2j here has 2j scalar g-return blocks and 4j physical H steps.

Run `computations/verify_balanced_charge.py`. It retains:

- 600 exact rational Dottie bisections and the new 768-bit four-branch
  invariance, separation and physical-image certificate.
- Exact zero-charge counts through 24 steps, anisotropic integer-weight
  counts through 20 steps, and twelve finite prime-clock traces.
- Three anisotropic elliptic/resolvent comparisons and three entire
  heat/Bessel comparisons at 130 digits, with their written series bounds.
- All 40 balanced inverse words of lengths two and four, with actual
  composition fixed points, derivatives, function/one-form traces and
  their cancellation, for isotropic and actual-quartet weights.
- The complete controlled approximation (32), retained term count and
  exact rational tail estimate. The full run took about 1.34 CPU seconds.

Primary texts are retained in `sources/balance/` with URL/SHA256 records;
the earlier Q_p proof and classified quartet source are frozen under its
`inputs/` directory. Ruelle's holomorphic trace identity is the published
operator input. The additional deductions here are the explicit charge
lift reproducing Q_p, its actual certified four-branch realization, the
anisotropic/Bessel charge kernels, prime-clock filters and the controlled
balanced joint product. The critical scalar lattice zeta and ordered
exponential-history invariants are developed in
[the ordered-history note](ordered-signed-histories.md). The exact
shifted-superzeta residue identity enters through (10).
