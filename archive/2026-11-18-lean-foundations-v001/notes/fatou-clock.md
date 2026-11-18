# A controlled fractional-iteration clock, phase recovery, and the two horn ends

**16 November 2026. Exact derivations, a quantitative analytic theorem, and directed computational checks.**

The Dottie germ has a computable Abel clock on an explicit attracting half-plane.
Its first two inverse-power coefficients recover the entire ordered logarithmic
phase rationally. The physical antiholomorphic half-step becomes a half-time
translation composed with reflection, and on the cylinder it exchanges the two
ends by reciprocal conjugation. These facts supply a quantitative analytic input
for the prime-adic solenoidal clock construction and an exact reduction of upper
and lower horn data to one another.

The existing canonical manuscript already contains the normalized germ,
antiholomorphic square root, iterative residue, and original-gauge cylinder
involution. The new work here is the explicit controlled Abel computation,
fractional-time inverse certificates, polynomial coefficient recurrence with
finite phase recovery, and the written horn-coefficient transfer.

## 1. Exact local object and the retained gauge

Let
\[
d=\cos d,\quad s=\sin d,\quad \alpha=s+id,\quad
\kappa=\frac{2\alpha}{1+\alpha}=1+i\beta,\quad
\beta=\frac d{1+s},\quad
\rho=\frac{s}{3(1+s)}=\frac{1-\beta^2}{6}.
\]
The original scalar return at its parabolic fixed point is conjugate to
\[
f(x)=\frac1\kappa\operatorname{expm1}
 \left(\frac\kappa{2-\kappa}
 \operatorname{expm1}((2-\kappa)x)\right),
\]
\[
f(x)=x+x^2+(1-\rho)x^3+\cdots.
\tag{1}
\]
The exact antiholomorphic half-step is
\[
K(x)=\frac{\operatorname{expm1}(\kappa\bar x)}\kappa,
\qquad K^2=f.
\tag{2}
\]
These are the canonical source's equations `normalized-germ` and
`normalized-halfstep`. Its compatible Fatou lift is
\[
\widehat K(W)=\bar W+\kappa/2.
\tag{3}
\]
In the original quotient coordinate \(\xi=e^{2\pi iW}\), this is
\[
J(\xi)=-r/\bar\xi,\qquad r=e^{-\pi\beta}.
\tag{4}
\]
The explicit constant gauge
\[
W_0=W-i\beta/4,\qquad \eta=e^{2\pi iW_0}=\xi/\sqrt r
\]
changes (3)–(4) to
\[
\boxed{\widehat K_0(W_0)=\bar W_0+\tfrac12,
\qquad J_0(\eta)=-1/\bar\eta.}
\tag{5}
\]
In particular, \(J_0\) has no fixed point on \(\mathbb C^*\), since a fixed
point would require \(|\eta|^2=-1\). It interchanges the cylinder ends
\(0\) and \(\infty\).

The source for the general antiholomorphic normal form, Fatou coordinates,
modulus, and root extraction is [Godin–Rousseau (2022), §§4–7](https://arxiv.org/pdf/2001.06428).
Equations (1)–(4) are already explicit in Nick's canonical Dottie manuscript.

## 2. The entire Touchard germ gives polynomial Abel coefficients

Write \(f(x)=\sum_{n\ge1}h_nx^n\). Substituting
\(\alpha=\kappa/(2-\kappa)\) into the existing Touchard formula gives
\[
\boxed{h_n(\kappa)=\frac1{n!}
\sum_{j=1}^n {n\brace j}\,
\kappa^{j-1}(2-\kappa)^{n-j}.}
\tag{6}
\]
Thus \(h_n\in\mathbb Q[\kappa]\), with degree at most \(n-1\), and
\(h_1=h_2=1\). The apparent endpoint phases in this polynomial expression
have removable continuations inherited from (6).

Use the attracting infinity coordinate \(t=-1/x\) and put
\[
B(w)=-f(-w)/w=1-w+h_3w^2-h_4w^3+\cdots,
\qquad F_\infty(t)=\frac{t}{B(1/t)}.
\]
Then
\[
F_\infty(t)=t+1+\rho/t+O(t^{-2}).
\]
Seek a clock of the form
\[
\Psi_N(t)=t-\rho\log t+\sum_{n=1}^N b_nt^{-n}.
\tag{7}
\]
The logarithm is the analytic branch on the right half-plane, real on its
positive real axis. Set \(A(w)=1/B(w)\) and define
\[
D_0(w)=\frac{A(w)-1-w}{w}+\rho\log B(w).
\]
Its constant and linear coefficients vanish. If \(b_1,\ldots,b_{n-1}\) have
already been computed, the next exact coefficient is
\[
\boxed{b_n=\frac1n[w^{n+1}]
 \left(D_0(w)+\sum_{j=1}^{n-1}b_jw^j(B(w)^j-1)\right).}
\tag{8}
\]
Indeed, the added term \(b_nw^n(B^n-1)\) begins with
\(-nb_nw^{n+1}\). Therefore (8) cancels that coefficient and produces
\[
\Psi_N(F_\infty(t))-\Psi_N(t)-1=O(t^{-N-2}).
\tag{9}
\]

Every operation in (8) is polynomial over \(\mathbb Q\). More precisely,
\[
\boxed{b_n\in\mathbb Q[\kappa],\qquad \deg b_n\le2n+2.}
\tag{10}
\]
For the degree proof, coefficients of \(B,1/B,\log B\) at order \(j\) have
degree at most \(j\). The residue \(\rho\) has degree two. In the induction
step, a term with \(b_j\), \(j<n\), has degree at most
\((2j+2)+(n+1-j)=n+j+3\le2n+2\). The remaining term has degree at most
\(n+3\le2n+2\).

For example,
\[
\boxed{b_1=-\frac{2\kappa^4-11\kappa^3+16\kappa^2-4\kappa-4}{72}.}
\tag{11}
\]
The exact symbolic script checks (6)–(10) through \(b_8\); the directed
numerical script constructs the recurrence through \(b_{64}\).

### Two clock coefficients recover the ordered phase

Put \(r_1=b_1,r_2=b_2\) and define
\[
\begin{aligned}
\mathcal A(r_1,r_2)={}&356400r_1^3+1296000r_1^2r_2-254592r_1^2\\
&-244620r_1r_2+25830r_1-928800r_2^2+22770r_2-757,
\end{aligned}
\]
\[
\begin{aligned}
\mathcal B(r_1,r_2)={}&5184000r_1^4-3404160r_1^3+5702400r_1^2r_2\\
&+314820r_1^2+20736000r_1r_2^2-2776680r_1r_2\\
&+7644r_1-7106400r_2^2+224100r_2-1183.
\end{aligned}
\]
Exact polynomial elimination yields
\[
\boxed{\kappa=\frac{\mathcal B(b_1,b_2)}{2\mathcal A(b_1,b_2)},
\qquad\alpha=\frac\kappa{2-\kappa}.}
\tag{12}
\]
The identity \(2\kappa\mathcal A-\mathcal B=0\) is checked symbolically on
the full coefficient family. At the actual Dottie value, directed arithmetic
gives
\[
\mathcal A(b_1,b_2)=-553.4446573906\ldots-756.3181316099\ldots i\ne0.
\]
Consequently, for the distinguished germ,
\[
\boxed{\mathbb Q(b_1,b_2)=\mathbb Q(\kappa)=\mathbb Q(\alpha).}
\tag{13}
\]
The first two inverse-power coefficients of the fractional-iteration clock
retain the full ordered phase field. Additive changes of Fatou gauge preserve
these coefficients.

## 3. A quantitative Abel coordinate on an explicit half-plane

This theorem converts the formal clock into a controlled analytic computation.

**Proposition.** For the distinguished Dottie germ, \(F_\infty\) is analytic
on \(\Re t>10\), maps that half-plane into itself, and satisfies
\[
\Re F_\infty(t)\ge\Re t+\tfrac12.
\tag{14}
\]
For every finite \(N\), the exact coefficients (8) and the explicitly defined
constant \(C_N\) below give an analytic clock
\[
\boxed{\Psi(t)=\Psi_N(t)+
\sum_{j=0}^\infty R_N(F_\infty^j(t)),
\quad R_N=\Psi_N\circ F_\infty-\Psi_N-1,}
\tag{15}
\]
with \(\Psi\circ F_\infty=\Psi+1\) and
\[
\boxed{|\Psi(t)-\Psi_N(t)|\le
C_N\left[(\Re t)^{-N-2}+\frac2{N+1}(\Re t)^{-N-1}\right].}
\tag{16}
\]
For \(N=64\), \(\Psi\) is univalent on \(\Re t>100\), with
\[
\boxed{|\Psi'(t)-1|<0.001343849376<1/100.}
\tag{17}
\]

### Proof and explicit constants

Fix \(r_0=1/10\), write \(m=|\kappa|\), and use the entire coefficient
majorant
\[
M(r)=\frac{\exp(\exp(mr)-1)-1}{m}.
\]
Coefficient by coefficient, \(|h_n|\) is bounded by the coefficient of this
majorant. Its linear coefficient is one and its quadratic coefficient is
\(m\). Hence for \(|w|\le r_0\),
\[
|f(-w)+w-w^2|\le C_3|w|^3,
\quad C_3=\frac{M(r_0)-r_0-mr_0^2}{r_0^3}.
\]
Set
\[
b=r_0+C_3r_0^2,
\qquad C_q=\frac{1+(1+r_0)C_3}{1-b}.
\]
Then \(|B(w)-1|\le b<1\) and
\[
\left|\frac{1/B(w)-1-w}{w}\right|\le C_q|w|.
\]
Directed arithmetic at 1024 bits verifies
\[
C_3<1.084158,\quad b<0.110842,
\quad C_q<2.465898,\quad C_qr_0<1/2.
\]
Thus \(B\) has no zero in the disk and (14) follows whenever
\(\Re t>10\).

The analytic function
\[
D_N(w)=\frac{1/B(w)-1-w}{w}+\rho\log B(w)
       +\sum_{n=1}^N b_nw^n(B(w)^n-1)
\]
vanishes to order \(N+2\), by (8). On \(|w|=r_0\) it is bounded by
\[
M_N=C_qr_0+|\rho|[-\log(1-b)]
 +\sum_{n=1}^N|b_n|r_0^n[(1+b)^n-1].
\]
The maximum principle applied to \(D_N(w)/w^{N+2}\) gives
\[
|R_N(t)|\le C_N|t|^{-N-2},\qquad C_N=M_N/r_0^{N+2}.
\]
Together with (14), this proves normal convergence of (15). Telescoping gives
the Abel equation. Comparing the positive decreasing series with an integral
gives (16).

To prove (17), differentiate \(\Psi_N\) explicitly and bound the derivative
of the correction by Cauchy's estimate on a circle of radius
\((\Re t-10)/2\). If \(E_N(R)\) denotes the bound in (16), then uniformly for
\(R=\Re t\ge100\),
\[
|\Psi'(t)-1|\le\frac{|\rho|}{R}
 +\sum_{n=1}^N\frac{n|b_n|}{R^{n+1}}
 +\frac{E_N((R+10)/2)}{(R-10)/2}.
\]
Each positive term decreases with \(R\). Evaluating it at \(R=100\), with
\(N=64\), proves the numerical bound (17). For two points of this convex
half-plane, integrate the derivative along their joining segment; the
deviation from their difference has modulus below \(0.01\) times its length.
Their images are distinct, proving univalence. ∎

This is a direct summable-defect construction for the specified germ. General
sectorial Fatou coordinates and their resurgent expansions are developed by
[Dudko–Sauzin (2014), §1, Theorem 1](https://arxiv.org/pdf/1307.8093).
The sign convention there uses a coefficient \(-\rho_{DS}/t\) at infinity;
here \(\rho_{DS}=-\rho\).

## 4. Certified fractional iteration and the physical half-step

On the clock domain, define
\[
F_\infty^\tau(t)=\Psi^{-1}(\Psi(t)+\tau)
\tag{18}
\]
whenever the target belongs to the selected clock image. It satisfies the
semigroup law on common domains. A fractional scalar return in the original
normalized coordinate is
\[
f^\tau(x)=-1/F_\infty^\tau(-1/x).
\]
The derivative in time is an analytic iterative-logarithm vector field,
\[
\frac{dx}{d\tau}=\frac1{\Phi'(x)}
=x^2-\rho x^3+(\rho^2+b_1)x^4+\cdots.
\tag{19}
\]

The finite clock (7) makes this computationally effective. Let a rational
decimal candidate \(t_\tau\) solve its truncated equation to high precision.
Directed evaluation bounds
\[
\delta=|\Psi_N(t_\tau)-\Psi_N(t)-\tau|
          +E_N(\Re t_\tau)+E_N(\Re t).
\]
With \(\varepsilon=0.001343849376\), a disk of radius
\(2\delta/(1-\varepsilon)\) about that candidate is a strict contraction ball
for \(u\mapsto u-[\Psi(u)-\Psi(t)-\tau]\), provided it stays in \(\Re u>100\).
It therefore contains exactly one actual fractional-time point.

Nine certificates pass: exact times \(1/3,1/2,1/5+i/10\), at starting points
\(t=200,200+30i,1000-80i\). At \(t=200\), the three certified radii are
respectively below \(9.674\times10^{-86}\), \(9.433\times10^{-86}\), and
\(9.877\times10^{-86}\). The analytic clock tail there is below
\(2.546121\times10^{-86}\). Point computations use 220 decimal digits;
directed coefficients and inequalities use 1024 bits.

In the \(t\)-coordinate the physical root is
\[
B_\infty(t)=-1/K(-1/t)
=\bar t+\kappa/2+O(1/\bar t).
\]
Its exact Abel law is
\[
\Psi(B_\infty(t))=\overline{\Psi(t)}+\kappa/2.
\tag{20}
\]
The same directed majorant calculation bounds
\(|B_\infty(t)-\bar t-\kappa/2|<1/10\) on \(\Re t>100\), so this
half-plane is also forward invariant under \(B_\infty\). To see the bound,
put \(u=\kappa/\bar t\) and expand
\((1-e^{-u})/u=1-u/2+e(u)\), with
\(|e(u)|\le(e^{|u|}-1-|u|-|u|^2/2)/|u|\).
The resulting elementary reciprocal estimate is recorded in the script.
One direct construction is to symmetrize any normalized Abel clock by the
involution
\[
\mathcal R\Psi(t)=\overline{\Psi(B_\infty(t))}-\bar\kappa/2.
\]
Because \(B_\infty^2=F_\infty\) and \(\Re\kappa=1\),
\(\mathcal R^2\Psi=\Psi\). Averaging with this involution gives (20), and
preserves the normalized asymptotic clock. Uniqueness with the given asymptotic
also follows by forward iteration and the vanishing difference at infinity.

After the unit gauge (5), the physical root is consequently
\[
\boxed{K=f^{1/2}\circ R,\qquad R^2=\operatorname{id},}
\tag{21}
\]
where \(R\) is reflection in the real Abel-time axis, transported back through
the clock. More generally, \(K\circ f^\tau=f^{\bar\tau}\circ K\) on common
domains. This retains the antiholomorphic phase when fractional iteration is
introduced.

## 5. One horn end determines the other

Choose the attracting and repelling Fatou charts with the compatible unit-gauge
root action \(A(W)=\bar W+1/2\). Let the upper and lower transition lifts be
\(T_+,T_-\). Since the physical root commutes with its square and exchanges
the overlap ends,
\[
\boxed{T_-\circ A=A\circ T_+.}
\tag{22}
\]
Write \(T_\pm(W)=W+N+S_\pm(e^{2\pi iW})\). Then
\[
\boxed{S_-(-1/\bar\eta)=\overline{S_+(\eta)}.}
\tag{23}
\]
For the multiplier and exponentiated horn maps this becomes
\[
m_-(-1/\bar\eta)=\overline{m_+(\eta)},
\qquad H_-\circ J_0=J_0\circ H_+.
\tag{24}
\]
If the upper end germ is \(S_+(\eta)=\sum_{n\ge0}a_n\eta^n\), then the
lower end germ has the exact expansion
\[
\boxed{S_-(\eta)=\bar a_0+
\sum_{n\ge1}(-1)^n\bar a_n\eta^{-n}.}
\tag{25}
\]
The gauge labels also have an explicit conversion. If the original upper
expansion is \(S_+^{\rm orig}(\xi)=\sum c_n\xi^n\), then
\(c_n=a_nr^{-n/2}\), since \(\eta=\xi/\sqrt r\). The original lower
coefficient at \(\xi^{-n}\) is therefore
\[
\boxed{(-1)^nr^{n/2}\bar a_n=(-r)^n\bar c_n.}
\]
This is an explicit upper/lower coefficient transfer,
useful for maintaining the physical phase and continuation labels in a horn
calculation. The two ends are exchanged; each end may carry several relevant
branches and Morse roots.

The underlying antiholomorphic modulus and its root symmetries are part of
[Godin–Rousseau's classification](https://arxiv.org/pdf/2001.06428). The
family-specific normalization (1)–(5) makes the transfer (23)–(25) explicit.

## 6. Tetration and fractional iteration: the exact dictionary

For ordinary towers \(T_a(z)=e^{az}\), with chosen logarithm \(a=\log b\),
an attracting fixed point \(z_*\) has the coordinate
\[
t=az_*,\quad z_*=e^t,\quad a=te^{-t},\quad T_a'(z_*)=t.
\]
Thus the multiplier is already the natural parameter. Baker and Rippon's
1983 theorem establishes cap-one convergence for \(a=te^{-t}\) when
\(|t|<1\), and also at root-of-unity boundary multipliers; their variable-base
stability theorem treats perturbations of the exponential coefficients.
[Original paper, Theorems 1–2](https://www.acadsci.fi/mathematica/Vol08/vol08pp179-186.pdf)

At a nonzero attracting multiplier \(\lambda\), a Schröder coordinate
\(\chi(T(z))=\lambda\chi(z)\) produces
\[
T^\tau(z)=\chi^{-1}(e^{\tau\operatorname{Log}\lambda}\chi(z)),
\]
with the logarithm branch retained. Passing to a logarithm of \(\chi\)
turns this into an Abel translation coordinate. At the Dottie multiplier one,
the clock (15) is the corresponding parabolic construction.

The functional equations have a common form:
\[
\Phi(T(z))=\Phi(z)+1,\qquad
\operatorname{Tet}(w)=\Phi^{-1}(w+C),\qquad
\operatorname{Tet}(w+1)=T(\operatorname{Tet}(w)).
\]
The exact reciprocal return therefore supplies sectorial reciprocal tetration,
with controlled fractional heights and a separately retained physical root.
Nick's foundations manuscript already gives the broader two-base conjugacy
to \(E_\kappa\circ E_{\kappa+\delta}\), keeping ordinary and reciprocal towers
as specified slices.

Historical primary anchors are [Euler's E489, presented 1777 and published
1778](https://scholarlycommons.pacific.edu/euler-works/489/),
[Koenigs (1884), functional linearization](https://www.numdam.org/articles/10.24033/asens.247/),
Kneser's 1950 paper *Reelle analytische Lösungen der Gleichung
\(\vartheta(\vartheta(x))=e^x\) und verwandter Funktionalgleichungen*,
[DOI](https://doi.org/10.1515/crll.1950.187.56), and
[Kouznetsov's 2009 contour-integral numerical tetration method](https://mizugadro.mydns.jp/PAPERS/2009analuxpRepri.pdf).
The quantitative theorem above concerns the displayed Dottie attracting
half-plane and the precise normalized germ (1).

## Reproduction

- `computations/verify_fatou_formal.py` checks the exact polynomial recurrence,
  degree bounds through order eight, and rational phase-recovery identity.
- `computations/verify_fatou_clock.py` constructs degree 64, proves the analytic
  inequalities with 1024-bit balls, checks integer/physical-half-step defects
  at 220 digits, and certifies nine actual fractional-time points.
- `computations/fatou-formal-results.json` and `fatou-clock-results.json` retain
  formulas, precision, all constants, and exact decimal candidate centers.

Both programs run headlessly in a few CPU seconds and leave the active lab and
earlier research packages untouched.
