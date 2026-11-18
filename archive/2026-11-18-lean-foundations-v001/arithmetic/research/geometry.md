# The two real circles and the complex torus in Nick's original curve

The original six coefficients produce a smooth genus-one curve whose compact real locus consists of **exactly two circles**. There is a short algebraic reason for that topology: its quartic is a strictly positive sum of two squares.

## 1. The exact quadratic and the quartic

Set

\[
N=465x^2-183x-659,\qquad D=155x^2+396x-936,
\]
\[
A=N-D=310x^2-579x+277,\quad B=N-3D=2149-1371x,
\quad C=-N-2D=2531-609x-775x^2.
\]

The original equation is \(P(x,y)=Ay^2+By+C=0\). Completing the square with **\(Y=2Ay+B\)** gives

\[
Y^2=f(x),\quad
f=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\]

The useful structural identity is

\[
\boxed{f=(N-D)^2+4N^2.}
\]

Indeed

\[
A=310\left(x-\frac{579}{620}\right)^2+\frac{8239}{1240}>0.
\]

Hence \(f(x)>0\) for every real \(x\). The exact Sturm sequence independently gives zero real roots. The ordinary polynomial discriminant is

\[
\operatorname{disc}(f)=2474894018773477950377523339416326400\ne0.
\]

Thus its four complex branch points are distinct and occur in two conjugate pairs. Their approximate positions are

\[
-0.85863553766403\pm0.475133227389942i,
\qquad
1.39960327959951\pm0.0328751628738127i.
\]

## 2. Why the real completion is exactly two circles

The two affine graphs \(Y=\pm\sqrt{f(x)}\) are disjoint and each projects bijectively to the real \(x\)-line. At infinity use

\[
t=1/x,\qquad V=Y/x^2.
\]

Then

\[
V^2=961000-1039740t-1810543t^2+644010t^3+1813853t^4.
\]

At \(t=0\) the two points are \(V=\pm310\sqrt{10}\). Because \(x^2>0\), the sign of \(V\) matches the sign of \(Y\) on both tails. Consequently the positive graph's two ends meet at its positive infinity point; the negative graph's ends meet at its negative infinity point. Each real line has acquired one point, giving a circle. Therefore

\[
\boxed{C(\mathbb R)\cong S^1\sqcup S^1.}
\]

In the original \((x,y)\)-coordinates these same curves are

\[
y_\pm(x)=\frac{-B(x)\pm\sqrt{f(x)}}{2A(x)}.
\]

They are finite and smooth for all real \(x\), and their two added points are

\[
\boxed{(x,y)=(\infty,+\sqrt{5/2}),\quad(\infty,-\sqrt{5/2}).}
\]

They are separated by \(y=-3/2\): \(y_+>-3/2\), \(y_-<-3/2\). One way to see it is to put \(s=2y+3\), \(k=4N/A\); the two roots of \(s^2-ks-1=0\) have opposite signs.

The point \((e,\widehat\pi)\) lies on the upper component. Its companion point at the same \(x=e\) has \(y=-1.55386082292392693746\ldots\). The upper coordinate is

\[
\widehat\pi=3.141592653589793238375823310552253075994\ldots.
\]

The natural compact embedding is in \(\mathbb{RP}^1\times\mathbb{RP}^1\), the product of the two real projective coordinate circles. In the affine plane each component appears as an open graph; its closure through the specified infinity point makes the circle visible intrinsically. The word “oval” here refers to a closed real component on the compact curve.

## 3. Why the complex completion is a torus

The map \((x,Y)\mapsto x\) has degree two and four simple complex branch points. Riemann–Hurwitz gives

\[
2g(C)-2=2(-2)+4=0,
\]

so \(g(C)=1\). The compact connected complex Riemann surface is therefore topologically a torus. Its real points form the two circles computed above. The compact complex surface and its real fixed locus have different real dimensions: two and one respectively.

For the binary-quartic framework, smooth weighted projective completion, and Jacobian model used below, see [Tom Fisher, *On binary quartics and the Cassels–Tate pairing*, section 2](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf).

## 4. A general theorem for this approximation architecture

**Two-circle lemma.** Let \(N_h,D_h\) be real homogeneous quadratic forms in \(X,Z\) with no common nonzero complex zero, and suppose the binary quartic

\[
\Delta_h=(N_h-D_h)^2+4N_h^2
\]

has four distinct complex projective roots. Then the smooth projective curve \(Y^2=\Delta_h(X,Z)\) has complex genus one and real locus \(S^1\sqcup S^1\).

**Proof.** On every real projective point, a zero of \(\Delta_h\) would force \(N_h=D_h=0\), which is excluded. Hence \(\Delta_h>0\) on the real projective line. The coordinate \(Y\) transforms as a quadratic form; between the two real base charts its transition factor is a nonzero square. Its positive and negative branches therefore glue separately to global sections. Each section is a copy of \(\mathbb{RP}^1\cong S^1\). Squarefreeness supplies four simple complex branch points, and the same Riemann–Hurwitz calculation gives genus one. ∎

For Nick's forms the resultant is exactly \(19096567765\ne0\), and the quartic discriminant above verifies the hypotheses. This gives a reusable geometric theorem for every coefficient vector in the same architecture satisfying the displayed hypotheses.

## 5. An explicit elliptic Jacobian and its complex structure

For a binary quartic \(aX^4+bX^3Z+cX^2Z^2+dXZ^3+eZ^4\), use

\[
I=12ae-3bd+c^2,\qquad
J=72ace+9bcd-27ad^2-27b^2e-2c^3.
\]

Here exact computation gives

\[
I=26204227623049,\qquad J=-268154656114324603786.
\]

The elliptic Jacobian has the model

\[
\boxed{v^2=u^3-707514145822323u+7240175715086764302222.}
\]

Its complex-structure invariant is

\[
\boxed{j=\frac{17993435433574642379718140848247531586649}
{9667554760833898243662200544595025}}
\approx1861218.87889079567267.
\]

This rational number is nonintegral. The Jacobian consequently has endomorphism ring \(\mathbb Z\) over \(\mathbb C\): a complex-multiplication elliptic curve has algebraic-integer \(j\), as in [Milne, *Modular Functions and Modular Forms*, Corollary 12.15](https://www.jmilne.org/math/CourseNotes/MF110.pdf). The Jacobian model and the genus-one quartic are related through the standard binary-quartic construction; specifying a rational origin on the quartic is a separate arithmetic task. Over \(\mathbb C\), a choice of any point identifies the genus-one curve with its Jacobian.

## 6. Two exact involutions

The original curve has commuting rational involutions

\[
\iota_x(x,y)=\left(\frac{333095x-432252}{212505x-333095},y\right),
\]
\[
\iota_y(x,y)=\left(x,-\frac{3y+5}{2y+3}\right).
\]

The second exchanges the two real circles: it sends \(s=2y+3\) to \(-1/s\). The first preserves each circle. Their common quotient coordinate is \(k=4N/(N-D)\), matching the field diamond in the earlier report. Exact polynomial substitutions verify both involutions and their squares.

## Reproduction

Run `geometry/verify_geometry.py`. It writes `geometry/geometry-results.json` containing the exact square completion, discriminant, resultant, Sturm sequence, invariants, involution checks, marked point, and illustrative branch decimals. Exact arithmetic supplies every topological decision; the decimals locate the already-certified algebraic objects.
