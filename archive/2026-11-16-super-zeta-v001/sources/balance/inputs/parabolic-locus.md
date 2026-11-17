# The complete multiplier-one fixed-pair locus and the Euler–Dottie phase dictionary

16 November 2026. Global analytic classification, exact symmetry, and directed
radial isolations. The locus in this note consists of **fixed pairs with scalar
multiplier one** for the actual reciprocal map.

The two Dottie parameters are the complete multiplier-one fixed-pair locus
inside the sharp disk
\[
\boxed{|L|<R_1,
\qquad R_1=6.74686801170400996160445811546115996061343731609\ldots.}
\]
Every remaining parameter occurs in an explicitly classified quartet, one point
in each open quadrant. Its radius is determined by a strictly increasing scalar
equation, and those radii grow like \(2\pi n\). The same fixed-pair coordinates
place the ordinary real-tower convergence endpoints and the Dottie pair on one
exact mixed-base neutral curve.

## 1. Exact phase parametrization of multiplier-one fixed pairs

Keep the ordered equations
\[
P=e^{LQ},\qquad Q=e^{-LP},\qquad
U=LQ,\quad V=-LP,\quad\mu=UV.
\]
At \(\mu=1\), put \(U=\alpha,V=1/\alpha\). The fixed equations are
equivalent to
\[
\boxed{\alpha^2e^{\alpha-1/\alpha}=-1,\qquad
L=-e^{-\alpha}/\alpha,\quad P=e^\alpha,\quad Q=e^{1/\alpha}.}
\tag{1}
\]
These compatibility and recovery identities are established in the existing
reciprocal/Dottie theorem note. This investigation solves their phase equation
globally in polar coordinates.

The two symmetries have exact parameter actions:
\[
L(\bar\alpha)=\overline{L(\alpha)},\qquad
L(1/\alpha)=-L(\alpha).
\tag{2}
\]
The first follows by conjugation. For the second, the ratio is
\(\alpha^2e^{\alpha-1/\alpha}=-1\).

## 2. Complete polar classification

**Theorem.** Let \(d=\cos d\), \(s=\sin d\). Every solution of (1) is
exactly one of the following:

1. The two unit phases \(s\pm id\), giving
   \(L=\pm i e^{-s}\).
2. For a unique integer \(n\ge1\), one of the four phases
   \[
   \boxed{\alpha=e^{\pm t_n\pm i\theta_n},}
   \tag{3}
   \]
   where
   \[
   \theta(t)=\arccos\!\left(-\frac{t}{\sinh t}\right)\in(\pi/2,\pi),
   \]
   \[
   \boxed{F(t_n):=\theta(t_n)+\cosh(t_n)\sin\theta(t_n)
   =\frac{(2n+1)\pi}{2}.}
   \tag{4}
   \]
   Each equation (4) has exactly one positive root. The four corresponding
   parameters are \(L_n,\bar L_n,-L_n,-\bar L_n\), all distinct, with
   \[
   \boxed{|L_n|=R_n=\exp(t_n\coth t_n),}
   \tag{5}
   \]
   and \(L_n\) in the open second quadrant. The radii \(R_n\) are strictly
   increasing.

### Proof

Write \(\alpha=e^{t+i\theta}\), with real \(t\) and principal angle
\(-\pi<\theta\le\pi\). Taking modulus and argument in (1) gives
\[
2t+2\sinh t\cos\theta=0,
\qquad
2\theta+2\cosh t\sin\theta\equiv\pi\pmod{2\pi}.
\tag{6}
\]
When \(t=0\), the second equation becomes
\(\theta+\sin\theta=(2m+1)\pi/2\). The function on the left is strictly
increasing from \(-\pi\) to \(\pi\), so its only targets are
\(\pm\pi/2\), each with one solution. For the positive solution,
\(\theta=\pi/2-d\), \(\sin\theta=d=\cos d\), giving
\(\alpha=\sin d+i d\). Equation (1) then gives \(L=i e^{-s}\).
Conjugation gives the other unit phase and parameter.

For \(t\ne0\), the first equation of (6) is
\(\cos\theta=-t/\sinh t\), an even function of \(t\). Thus reciprocal
and conjugation symmetry reduce the problem to \(t>0\),
\(\theta=\theta(t)\in(\pi/2,\pi)\).

Set
\[
q(t)=\sqrt{\sinh^2t-t^2}>0,\qquad h(t)=t\coth t>1.
\]
Differentiation gives
\[
\theta'(t)=-\frac{h(t)-1}{q(t)}<0,
\]
\[
\boxed{F'(t)=q(t)+\frac{(h(t)-1)^2}{q(t)}>0.}
\tag{7}
\]
Indeed \(1+\cosh t\cos\theta=1-h(t)\), and
\(\sinh t\sin\theta=q(t)\). Also
\(F(0+)=\pi\) and \(F(t)\to\infty\). The attainable half-integer targets
in (6) are therefore exactly those in (4), one for each \(n\ge1\).
This proves completeness and uniqueness of (3).

The parameter modulus from (1) is
\[
\log|L|=-e^t\cos\theta-t
=\frac{te^t}{\sinh t}-t=t\coth t.
\]
Moreover
\[
h'(t)=\frac{\sinh t\cosh t-t}{\sinh^2t}>0,
\]
so the radii are strictly increasing.

For \(\alpha=e^{t_n+i\theta_n}\), reduction of its parameter argument using
(4) gives the actual angle
\[
\boxed{\phi_n=\theta_n+e^{-t_n}\sin\theta_n.}
\tag{8}
\]
It is greater than \(\pi/2\). If \(u=\pi-\theta_n\in(0,\pi/2)\), then
\(e^{-t_n}\sin\theta_n=e^{-t_n}\sin u<u\), hence \(\phi_n<\pi\).
Thus \(L_n\) is strictly in the second quadrant. Its conjugate and negatives
occupy the other three quadrants; none coincide. Distinct n give distinct
radii, completing the classification. ∎

Every listed parameter has exactly one ordered multiplier-one fixed pair.
For the scalar map, direct differentiation gives
\[
g_L''(P)=-L(1+\alpha).
\]
The phase \(\alpha=-1\) does not solve (1), so every such fixed point is
simple parabolic. This agrees with the earlier local theorem and now has a
complete global enumeration.

## 3. The sharp fixed-pair isolation disk

Since \(t\coth t>1\), every nonunit phase gives \(|L|>e\). The first
actual radius is sharper:
\[
t_1=1.80936134129570331901627610019401132560007622440538\ldots,
\]
\[
\boxed{R_1=6.74686801170400996160445811546115996061343731609083\ldots.}
\]
The second-quadrant parameter is
\[
\boxed{L_1=-4.76696906335453755797551090309410843028068852420756
+4.77454017852772745834025019390963526040233300789084\,i.}
\]
The other three points follow by (2). The disk \(|L|<R_1\) consequently
contains precisely the two Dottie multiplier-one fixed-pair parameters.
At its boundary, the first nonunit quartet appears.

The first radii are

| n | \(R_n\), abbreviated |
|---:|---:|
|1|6.746868011704009961604458115461|
|2|13.150110190275139795188164338719|
|3|19.421357652181694070311954114184|
|4|25.675431020220608653570605265709|
|8|50.702736932266582280777156642132|

Each retained t-bracket comes from 500 exact rational bisections with directed
sign decisions at 1024 bits. The proof of strict monotonicity turns every
bracket into a unique radial-root enclosure. The script checks all four phases
and parameters, their compatibility equation and their common modulus.

## 4. Asymptotic geometry of the quartet sequence

Let \(A_n=2\pi n\), \(\ell_n=\log A_n\). As \(t\to\infty\),
\[
\theta(t)=\frac\pi2+2te^{-t}+O(t^3e^{-3t}),
\]
\[
F(t)=\frac{e^t}{2}+\frac\pi2+
(2t+\tfrac12-t^2)e^{-t}+O(t^4e^{-3t}).
\tag{9}
\]
Solving \(F(t_n)=A_n/2+\pi/2\) gives
\[
e^{t_n}=A_n+\frac{2\ell_n^2-4\ell_n-1}{A_n}
 +O(\ell_n^4/A_n^3),
\qquad t_n=\ell_n+O(\ell_n^2/A_n^2).
\]
Using \(\exp(t\coth t)=e^t+2te^{-t}+O(t^2e^{-3t})\) yields
\[
\boxed{R_n=A_n+
\frac{2\ell_n^2-2\ell_n-1}{A_n}
 +O(\ell_n^4/A_n^3).}
\tag{10}
\]
In particular \(R_n\sim2\pi n\).

Equation (8) also gives
\[
\boxed{\Re L_n=-2\log(2\pi n)-1+
O((\log n)^2/n^2),}
\]
\[
\boxed{\Im L_n=2\pi n-
\frac{4\log(2\pi n)+3/2}{2\pi n}
 +O((\log n)^4/n^3).}
\tag{11}
\]
For (9), expand \(t/\sinh t\), \(\arccos(-x)=\pi/2+\arcsin x\), and
\(\sin\theta=\sqrt{1-(t/\sinh t)^2}\). All expansions have controlled
remainders for sufficiently large t. The implicit correction has size
\(O(t^2e^{-2t})\), and substitution preserves the stated remainder orders.
For the real-part remainder in (11), retain the next term of the angle.
Writing \(r=e^t\), expansion of (8) gives
\[
\phi-\pi/2=\frac{2t+1}{r}
+\frac{\tfrac43t^3-2t^2+2t}{r^3}+O(t^5/r^5).
\]
Combining this with the radius expansion yields the cancellation
\[
\Re L=-2t-1-\frac{3t-1/6}{r^2}+O(t^5/r^4),\qquad
\Im L=r-\frac{2t^2+1/2}{r}+O(t^4/r^3).
\]
Substitution of
\(r=A_n+(2\ell_n^2-4\ell_n-1)/A_n+O(\ell_n^4/A_n^3)\)
therefore gives, more precisely,
\[
\Re L_n=-2\ell_n-1+
\frac{-4\ell_n^2+5\ell_n+13/6}{A_n^2}
+O(\ell_n^5/A_n^4),
\]
which proves the stated real-part bound. The imaginary-part expansion gives
the second formula of (11).

The directed/point records include n=16,64,256,1024 as well as the first
eight roots. At n=1024, the radius correction (10) has absolute error below
\(5.268\times10^{-9}\); the imaginary-part correction (11) has error below
\(8.361\times10^{-9}\). Those finite errors are numerical checks of the
derived asymptotic formulas.

## 5. A deformed Lambert-W form

The same phase equation has an exact square-root form. For the upper large
phase in (3), equation (4) determines the sign:
\[
\alpha_n e^{\alpha_n/2-1/(2\alpha_n)}=(-1)^n i.
\]
Consequently, on the continued upper Lambert sheet,
\[
\boxed{\alpha_n=2W_{\lceil n/2\rceil}
\left(\frac{(-1)^ni}{2}\,e^{1/(2\alpha_n)}\right).}
\tag{12}
\]
The branch label follows from
\(\arg\alpha_n+\Im(\alpha_n)/2-\Im(1/(2\alpha_n))
=(2n+1)\pi/2\), retaining the principal argument of the displayed
Lambert input. More explicitly, the imaginary part of
\(\alpha_n/2+\operatorname{Log}(\alpha_n/2)\) exceeds the principal
argument of that input by
\[
\frac{(2n+1)\pi}{2}-\frac{(-1)^n\pi}{2}
=2\pi\lceil n/2\rceil.
\]
This is a direct deformation of the ordinary exponential
fixed-point Lambert-W equation and a useful high-index initialization.
The polar theorem (3)–(8) supplies its global phase labeling.

For Lambert-W definitions and logarithmic branch conventions, see
[Corless et al., *On the Lambert W function* (1996)](https://cs.uwaterloo.ca/research/tr/1993/03/W.pdf).
The earlier foundations manuscript already uses a branch-retaining Lambert-W
atlas for general reciprocal fixed-pair recovery.

## 6. One mixed-base neutral curve contains both Euler endpoints and Dottie

The broader paired family is
\[
\mathcal F_{L,c}(P,Q)=(e^{LQ},e^{cLP}),\qquad
g_{L,c}(z)=e^{L e^{cLz}},\quad L,c\ne0.
\]
For ordinary exponentials, take \(T_L(z)=e^{Lz}\), where \(L\) is the chosen
logarithm of the tower base. Then \(c=1\) gives \(g_{L,1}=T_L^2\), while
\(c=-1\) gives the reciprocal return.

Choose \(\gamma,\delta\) with \(e^\gamma=L,e^\delta=c\), and define
\(E_\gamma(u)=e^u+\gamma\), \(C(z)=\gamma+cLz\). Direct composition gives
\[
\boxed{C\circ g_{L,c}\circ C^{-1}
=E_\gamma\circ E_{\gamma+\delta}.}
\tag{13}
\]
This is the common two-base coordinate dictionary already established in
NuckyDucky's foundations manuscript, with the ordinary and reciprocal slices and
the order of their stages retained.

At a multiplier-one fixed pair, set
\(U=LQ=\alpha,V=cLP=1/\alpha\). Recovery is
\[
\boxed{L=\alpha e^{-1/\alpha},\qquad
c=\alpha^{-2}e^{1/\alpha-\alpha}.}
\tag{14}
\]
On the unit phase \(\alpha=e^{i\theta}\), these formulas become
\[
\boxed{L(\theta)=e^{-\cos\theta}
e^{i(\theta+\sin\theta)},\qquad
c(\theta)=e^{-2i(\theta+\sin\theta)}=\bar L/L.}
\tag{15}
\]
Thus the same exact neutral curve contains:

| Tower slice | Unit phase | Parameter and tower base |
|---|---|---|
|Ordinary, \(c=1\)|\(\alpha=1\)|\(L=1/e\), base \(e^{1/e}\)|
|Ordinary, \(c=1\)|\(\alpha=-1\)|\(L=-e\), base \(e^{-e}\)|
|Reciprocal, \(c=-1\)|\(\alpha=s\pm id\)|\(L=\pm i e^{-s}\)|

For a one-base fixed point, its multiplier \(t\) satisfies
\(L=te^{-t}\). The ordinary entries are its multipliers \(+1\) and \(-1\),
the two classical real convergence endpoints. The reciprocal entries occur
when \(\theta+\sin\theta=\pm\pi/2\), exactly the Dottie equation.

There is also a precise local distinction along this family:
\[
g_{L,c}''(P)=cL(1+\alpha).
\]
The ordinary lower endpoint \(\alpha=-1\) has vanishing quadratic term in
the two-step return; its relative coordinate return begins
\(x-x^3/6+\cdots\). The reciprocal compatibility equation excludes
\(\alpha=-1\), so all its fixed multiplier-one points are simple.

The alternating-conjugate curve \(c=\bar L/L\), its boundary role, and the
physical antiholomorphic half-step belong to Baker and Rippon's earlier
composite exponential work, as credited in the canonical manuscripts.
The present formulas exhibit the exact Euler–Dottie dictionary in retained
phase coordinates. For ordinary tower convergence see
[Baker–Rippon (1983), Theorems 1–2](https://www.acadsci.fi/mathematica/Vol08/vol08pp179-186.pdf);
the canonical foundations source identifies the 1989 composite-map theorem.

## Reproduction and precision

`computations/verify_parabolic_locus.py` isolates 12 radial roots using
500 exact rational bisections and 1024-bit interval signs; it checks the
48 phase/parameter reconstructions and compares independent 220-digit
calculations. Complete brackets, parameters, residuals, and asymptotic errors
are retained in `computations/parabolic-locus-results.json`.

The analytic monotonicity proof supplies the complete global classification.
The interval calculations isolate particular members and establish the
displayed sharp first radius. The run takes well under one CPU second and
uses no application, GUI, or GPU resources.
