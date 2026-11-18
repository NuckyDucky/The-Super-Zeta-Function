# The quarter-shift trajectory has one global discrete Hurwitz sign transition

16 November 2026. Retain the actual nonunit quartet radii and the normalized
levels
\[
B_n=4^{-n}\binom{2n}{n},\qquad
\Lambda_n=\frac{nR_nB_n^2}{2},\qquad
\delta_n=n-\Lambda_n.
\]
The observable in this note is
\[
H(\delta)=\zeta(-1,1-\delta)=\zeta(-1,\delta)
=-\frac1{12}+\frac\delta2-\frac{\delta^2}{2}.
\tag{1}
\]
It is invariant under both quartet sign actions, because all four phases
share the same radius \(R_n\). The transition proved below therefore
occurs simultaneously in the four retained symmetry labels.
The associated unit-spacing model is \(n-\delta\), \(n\ge1\), so its
Hurwitz argument is \(1-\delta\). At order \(-1\), the Bernoulli
reflection \(B_2(1-\delta)=B_2(\delta)\) gives the displayed equality.
Complex-order continuation retains the argument \(1-\delta\).
Its two real zeros are \((1\pm1/\sqrt3)/2\). On the interval
\(0<\delta<1/4\), it is strictly increasing and has the unique zero
\[
\delta_c=\frac{1-1/\sqrt3}{2}
=0.2113248654051871177454256097490212721761\ldots.
\tag{2}
\]
The Bernoulli-polynomial formula for the Hurwitz value is
[NIST DLMF 25.11.14](https://dlmf.nist.gov/25.11.E14).

## 1. Global discrete theorem

**Theorem.** For the classified nonunit reciprocal quartets:

1. \(0<\delta_n<1/4\) for every positive integer n, and
   \(\delta_n\to1/4\).
2. The unique global minimum over the positive integer levels is
   \[
   \boxed{\delta_2=
   0.15076575449255846630166438986769366666540551172627712\ldots.}
   \]
3. The complete discrete sign pattern is
   \[
   \boxed{H(\delta_n)<0\quad(1\le n\le28),\qquad
   H(\delta_n)>0\quad(n\ge29).}
   \tag{3}
   \]
4. A uniform infinite-tail estimate is
   \[
   \boxed{\delta_n>
   0.2259130442824248614871209817580486015566\ldots
   \quad(n\ge128).}
   \tag{4}
   \]

The proof combines an elementary all-index radius inequality, the existing
strict gamma/Cauchy estimates, and directed verification of the finite
prefix \(1\le n\le127\).

## 2. An elementary radius inequality controls the upper boundary

Use the retained continuous counting parameter
\[
\theta(t)=\arccos(-t/\sinh t),\quad
F(t)=\theta(t)+\cosh t\sin\theta(t),\quad
A(t)=2F(t)-\pi,
\]
\[
R(t)=e^{t\coth t},\qquad A(t_n)=2\pi n.
\]
We first prove
\[
\boxed{R(t)>A(t)\qquad(t\ge2).}
\tag{5}
\]
Let \(r=e^t\) and \(a=t/\sinh t\). For \(t\ge2\),
\(a\le2/\sinh2<3/5\), so
\[
\sqrt{1-a^2}\le1-a^2/2,
\qquad \arcsin a\le a/\sqrt{1-a^2}\le5a/4.
\]
Consequently,
\[
A=2\arcsin a+2\cosh t\sqrt{1-a^2}
\le r+r^{-1}-\cosh(t)a^2+\frac52a.
\]
On the other hand
\[
R=r\exp\!\left(\frac{2t}{r^2-1}\right)\ge r+a.
\]
Since \(e^{-2t}<1/25\), one has
\(a\le25t/(12r)\), while
\(\cosh(t)/\sinh^2t\ge2/r\). Therefore
\[
R-A\ge\frac1r\left(2t^2-\frac{25}{8}t-1\right)>0,
\]
because the polynomial is positive and increasing for \(t\ge2\).
The directed prefix proves \(t_2>2\), and monotonicity of \(t_n\)
extends this to every \(n\ge2\). The remaining level n=1 is checked
directly. Thus
\[
\boxed{R_n>2\pi n\quad(n\ge1).}
\tag{6}
\]

Write \(D_n=\pi nB_n^2\). The exact positive-kernel identity from the
binomial-normalization theorem is
\[
\log D_n=-\int_0^\infty e^{-nt}\frac{\tanh(t/4)}t\,dt.
\]
Using \(\tanh(t/4)<t/4\) gives \(D_n>e^{-1/(4n)}\). Hence
\[
\Lambda_n=n\frac{R_n}{2\pi n}D_n
>ne^{-1/(4n)}>n-1/4,
\]
which proves \(\delta_n<1/4\) at every level.

## 3. A uniform lower bound closes the infinite tail

Put
\[
L=\log(2\pi n),\quad A=2\pi n,\quad
\eta_n=\frac{256(1+L)^2}{A^2}.
\]
The proved radial inverse disk
\(\rho_L=[256(1+L)^2]^{-1}\), with \(|\chi(L,x)|<1/8\), gives
\[
0<\chi_n:=\log(R_n/A)
\le U_n:=\frac{2L^2-2L-1}{A^2}
+\frac{\eta_n^2}{8(1-\eta_n)}
\quad(\eta_n<1).
\tag{7}
\]
The strict gamma-kernel remainder gives
\[
-\frac1{4n}<\log D_n<-
\frac1{4n}+\frac1{96n^3}.
\]
Let \(u_n=\log[\Lambda_n/n]=\chi_n+\log D_n\). For \(n\ge128\)
the bounds below show
\[
-\frac1{4n}<u_n<-
\frac1{4n}+U_n+\frac1{96n^3}<0.
\]
For negative u, \(e^u\le1+u+u^2/2\). It follows that
\[
\boxed{\delta_n=n(1-e^{u_n})>
\frac14-nU_n-\frac1{96n^2}-\frac1{32n}.}
\tag{8}
\]

Every subtracted term on the right decreases for \(n\ge128\).
For the first part of \(nU_n\), differentiation with respect to
\(\log n\) gives the sign of
\(-2L^2+6L-1\), which is negative for
\(L>(3+\sqrt7)/2\). For its second part,
\[
n\eta_n^2\ \text{ is proportional to }\ (1+L)^4n^{-3},
\]
which decreases when \(L>1/3\); also \(\eta_n\) decreases, so its
denominator \(1-\eta_n\) increases. The two remaining inverse powers
decrease directly.

At n=128, directed arithmetic gives
\[
\eta_{128}=0.02340466891\ldots<1,
\]
and the right side of (8) is the value in (4). In particular it is
strictly above \(\delta_c\), above zero, and above \(\delta_2\).
It also proves \(nU_n+1/(96n^2)<1/4\), used to establish \(u_n<0\).
This closes the whole infinite tail using a single explicit bound.

The two analytical inputs in this section are retained, with their full
proofs and numerical gates, in the earlier
[radial-zeta disk theorem](../../2026-11-16-super-zeta-v001/sources/foundation/radial-zeta.md)
and the
[strict binomial kernel theorem](../../2026-11-16-super-zeta-v001/research/binomial-normalization.md).

## 4. Directed finite prefix and the global conclusions

`computations/verify_global_quarter_shift.py` uses 512-bit directed
arithmetic and 360 exact rational bisections for every \(t_n\),
\(1\le n\le127\). It evaluates \(B_n\) from its exact integer binomial
coefficient and checks:

- Every \(R_n>2\pi n\), \(0<\delta_n<1/4\), and \(t_2>2\).
- Every \(H(\delta_n)<0\) for \(n\le28\), and every
  \(H(\delta_n)>0\) for \(29\le n\le127\).
- Every \(\delta_n>\delta_2\) in that prefix except n=2.
- Every scalar inequality entering the bound for all \(n\ge128\).

Because H is increasing on \((0,1/4)\), (4) gives H positive throughout
the remaining tail. The same bound exceeds the finite-prefix minimum.
This proves the complete theorem.

The limiting quarter boundary follows from the controlled expansion
\[
\delta_n=\frac14-
\frac{1/32+(2L_n^2-2L_n-1)/(4\pi^2)}{n}
+O((\log n)^2/n^2),\qquad L_n=\log(2\pi n).
\tag{9}
\]
Thus \(\delta_n\to1/4\) through the strict interval proved above, and
\(H(\delta_n)\to\zeta(-1,3/4)=\zeta(-1,1/4)=1/96\).

## 5. The continuous radial interpolation and characteristic geometry

For real \(x>1/2\), define t(x) by
\(F(t)=\pi(x+1/2)\), and use the gamma interpolation
\[
B(x)=\frac{\Gamma(x+1/2)}{\sqrt\pi\,\Gamma(x+1)},\qquad
\Lambda(x)=\frac{xR(t(x))B(x)^2}{2},\qquad
\delta(x)=x-\Lambda(x).
\]
This is the continuous counting/radial interpolation; the actual
characteristic quartets are its integer sections.

The interpolation has an exact phase identity. Define
\[
\alpha_{\sigma,\tau}(x)=
\exp\!\left(\sigma t(x)+i\tau\theta(t(x))\right),
\qquad\sigma,\tau\in\{1,-1\}.
\]
The real part of twice the lifted phase equation is
\(2\sigma[t+\sinh t\cos\theta]=0\), and its imaginary part is
\(2\tau F(t)=2\pi\tau(x+1/2)\). Therefore
\[
\boxed{\alpha_{\sigma,\tau}(x)^2
\exp\!\left(\alpha_{\sigma,\tau}(x)
-\alpha_{\sigma,\tau}(x)^{-1}\right)
=-e^{2\pi i\tau x}.}
\tag{9a}
\]
This gives precisely the original characteristic equation at integer x.
The observable \(H(\delta(x))\) is invariant under the two independent
sign actions. At the certified continuous crossing \(x_*\in(28,29)\),
the four distinct marked interpolating phase points consequently map to
the same Hurwitz zero
\[
\zeta(-1,a_*)=0,\qquad
a_*=1-\delta_c=\frac{1+1/\sqrt3}{2}.
\]
The integer characteristic sections and this continuous observable
crossing are both specified by (9a).

Let \(h(t)=t\coth t\),
\(q(t)=\sqrt{\sinh^2t-t^2}\). The exact derivative is
\[
F'(t)=q(t)+\frac{(h(t)-1)^2}{q(t)}>0,
\quad h'(t)=\coth t-t\operatorname{csch}^2t>0,
\]
\[
\boxed{\delta'(x)=1-\Lambda(x)
\left[\frac{\pi h'(t)}{F'(t)}+\frac1x
+2\psi(x+1/2)-2\psi(x+1)\right].}
\tag{10}
\]
The gamma portion also equals the derivative of the positive-kernel
\(\log D(x)\), so all branches and real domains are specified.
Differentiating the controlled analytic expansion gives
\[
\delta'(x)=\frac{1/32+(2L^2-6L+1)/(4\pi^2)}{x^2}
+O((\log x)^2/x^3),\quad L=\log(2\pi x),
\]
and therefore eventual positive derivative. A separately labeled
100-digit point calculation finds a stationary interpolation point
\[
x\approx1.7501000640313835237599175782069865815244,
\quad\delta(x)\approx0.1504583259700265658835271270434556474568.
\]
The global discrete minimum and sign theorem above use their own
directed finite-prefix/infinite-tail proof.

The characteristic phase equation also stays regular at every listed
root. If
\(\Phi(\alpha)=\alpha^2e^{\alpha-1/\alpha}+1\), then at a root
\[
\boxed{\Phi'(\alpha)=-\frac{(\alpha+1)^2}{\alpha^2}\ne0.}
\tag{11}
\]
Indeed \(\Phi(-1)=2\). The classified phase quartets have simple roots,
while (3) records the exact sign transition of their specified
quarter-shift/Hurwitz observable.

The complete precision record, all 127 rational brackets, finite signs,
minimum comparisons and infinite-tail gates are retained in
`computations/global-quarter-shift-results.json`. The verifier runs in
about 0.44 CPU seconds.
