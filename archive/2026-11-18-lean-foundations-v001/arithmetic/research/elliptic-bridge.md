# The reciprocal field square carries a rational 2-isogeny

**16 November 2026. Exact structural deduction and reproducible polynomial verification.**

The original six-coefficient approximation architecture forces a distinguished rational 2-torsion direction on its elliptic Jacobian. The two commuting sheet exchanges already visible in the field diamond combine into a degree-two map between genus-one curves. Their Jacobians are the two explicitly 2-isogenous elliptic curves

\[
\boxed{E_0:\quad y^2=x^3+5028677x^2-305545084240x,}
\]
\[
\boxed{E'_0:\quad y^2=x^3-10057354x^2+26509772707289x.}
\]

This deduction supplies an arithmetic operation attached to the user's original curve: its reciprocal quadratic symmetries select a concrete elliptic 2-isogeny. The same construction works for every smooth quartic obtained as the norm of two quadratic forms.

The source for the original curve, field square and involutions is [the existing coefficient-fields report](../../notes/sources/coefficient-fields-report.md), section 4, and [the existing geometry report](geometry.md). The standard binary-quartic Jacobian convention used there, and retained here, is \(v^2=u^3-27Iu-27J\); see [Tom Fisher, *On binary quartics and the Cassels–Tate pairing*, section 2](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf). All additional identities below are checked by [verify_elliptic.py](../computations/verify_elliptic.py), with exact output in [elliptic-results.json](../computations/elliptic-results.json).

## 1. A general norm-quartic proposition

Let

\[
A(X,Z)=aX^2+bXZ+cZ^2,\qquad
B(X,Z)=dX^2+eXZ+fZ^2,
\]

and let \(t\in\mathbb Q^*\). Define

\[
\delta_A=b^2-4ac,\qquad \delta_B=e^2-4df,
\qquad m=be-2af-2cd,
\]
\[
R=\operatorname{Res}(A,B)
=(af-cd)^2-(ae-bd)(bf-ce),
\]
\[
q=\delta_A+t\delta_B,\qquad
D=(\delta_A-t\delta_B)^2+4tm^2.
\]

Assume the binary quartic \(F=A^2+tB^2\) is nonsingular. Equivalently,

\[
\boxed{tRD\ne0,\qquad
\operatorname{disc}(F)=16t^2R^2D.}
\tag{1}
\]

**Proposition.** The smooth genus-one curve \(C:Y^2=F\) has Jacobian isomorphic over \(\mathbb Q\) to

\[
\boxed{E_0:\quad y^2=x^3+qx^2-4tRx.}
\tag{2}
\]

The point \(T=(0,0)\) has order two, and the quotient by its translations is

\[
\boxed{E'_0:\quad y'^2=x'^3-2qx'^2+(q^2+16tR)x'.}
\tag{3}
\]

For \(x\ne0\), the degree-two isogeny is

\[
\boxed{x'=x+q-\frac{4tR}{x},\qquad
 y'=y\frac{-4tR-x^2}{x^2}.}
\tag{4}
\]

It extends to the smooth completions and has kernel \(\{O,T\}\).

### Proof: the invariant calculation

Write

\[
F=A_4X^4+B_4X^3Z+C_4X^2Z^2+D_4XZ^3+E_4Z^4.
\]

Its coefficients are

\[
\begin{aligned}
A_4&=a^2+td^2,&B_4&=2ab+2tde,\\
C_4&=b^2+2ac+t(e^2+2df),\\
D_4&=2bc+2tef,&E_4&=c^2+tf^2.
\end{aligned}
\]

For the standard invariants

\[
I=12A_4E_4-3B_4D_4+C_4^2,
\]
\[
J=72A_4C_4E_4+9B_4C_4D_4-27A_4D_4^2
-27B_4^2E_4-2C_4^3,
\]

expansion and collection give

\[
\boxed{I=q^2+12tR,\qquad
J=-2q^3-36tRq.}
\tag{5}
\]

The script verifies these as multivariate polynomial identities over the exact ring \(\mathbb Z[a,b,c,d,e,f,t]\). Therefore the cubic of the standard Jacobian factors as

\[
\boxed{u^3-27Iu-27J
=(u-3q)(u^2+3qu-18q^2-324tR).}
\tag{6}
\]

Substitute

\[
u=9x+3q,\qquad v=27y.
\]

The Jacobian equation becomes (2). This gives the asserted rational order-two point directly.

Also

\[
m^2-\delta_A\delta_B=4R,
\qquad q^2+16tR=D.
\tag{7}
\]

Using \(27\operatorname{disc}(F)=4I^3-J^2\), equations (5)–(7) give (1). In particular \(R\ne0\), so the order-two point is nonsingular.

To verify (4), put \(a_0=q,b_0=-4tR\) and \(S=x^2+a_0x+b_0\). Then \(y^2=xS\) and \(x'=S/x\). After multiplication by \(x^4\), the target equation is precisely

\[
xS(b_0-x^2)^2
=xS\{S^2-2a_0xS+(a_0^2-4b_0)x^2\},
\]

because the expression in braces is \((x^2-b_0)^2\). The rational map sends \(O\) and \((0,0)\) to the point at infinity, and its degree is two. Equivalently, translation by \(T\) is

\[
\tau_T(x,y)=\left(\frac{b_0}{x},-\frac{b_0y}{x^2}\right).
\]

Both functions in (4) are invariant under this involution, which identifies their map with the order-two quotient. ∎

### Why the rational torsion is structural

Over \(\mathbb Q(\sqrt{-t})\), the quartic factors into two quadratics:

\[
F=(A+\sqrt{-t}\,B)(A-\sqrt{-t}\,B).
\]

Their two root pairs form a Galois-stable partition of the four branch points. A partition into two unordered pairs determines a nonzero 2-torsion point of the elliptic Jacobian. Galois may exchange the two blocks, and an order-two point equals its own negative; the selected point is consequently rational. Formula (6) computes that point in the invariant model.

Thus the resultant controls smoothness and the numerical elliptic coefficients. The norm factorization itself supplies the distinguished rational 2-torsion direction.

For the user's architecture,

\[
A=N-D,\quad B=N,\quad t=4,
\]

so

\[
q=\operatorname{disc}(N-D)+4\operatorname{disc}(N),
\quad R=\operatorname{Res}(N,D),
\]

and the general models simplify to

\[
E_0:y^2=x^3+qx^2-16Rx,
\quad
E'_0:y'^2=x'^3-2qx'^2+(q^2+64R)x'.
\tag{8}
\]

## 2. The original six integers determine the isogeny explicitly

Use

\[
N(x)=465x^2-183x-659,\quad D(x)=155x^2+396x-936,
\]
\[
A=N-D=310x^2-579x+277,\qquad B=N.
\]

The exact values are

\[
\delta_A=-8239,\quad\delta_B=1259229,\quad
q=5028677,\quad R=19096567765.
\]

The previous Jacobian model was

\[
v^2=u^3-707514145822323u+7240175715086764302222.
\]

Its cubic factors as

\[
(u-15086031)(u^2+15086031u-479925814489362).
\]

Consequently its rational order-two point is \((15086031,0)\). The isomorphism

\[
u=9x+15086031,\qquad v=27y
\]

gives exactly the smaller model displayed at the start. Its quotient isogeny is

\[
x'=x+5028677-\frac{305545084240}{x},
\quad
 y'=y\frac{-305545084240-x^2}{x^2}.
\tag{9}
\]

The remaining two geometric 2-torsion points have quadratic discriminant

\[
26509772707289=41\cdot457\cdot1414835497.
\]

This is nonsquare, so the rational 2-torsion subgroup is exactly \(\mathbb Z/2\mathbb Z\). The companion arithmetic investigation records the good-reduction point counts and the full rational torsion determination.

## 3. The known reciprocal field square produces the quotient curve

The original approximation curve is

\[
P(x,y)=(N-D)y^2+(N-3D)y-N-2D=0.
\]

Its previously established common quotient coordinate is

\[
k=\frac{4N(x)}{N(x)-D(x)},\qquad s=2y+3.
\]

Over \(\mathbb Q(k)\), the two quadratic subfields are specified by

\[
(310k-1860)x^2+(732-579k)x+277k+2636=0,
\]
\[
s^2-ks-1=0.
\]

Their discriminants are

\[
\Delta_x(k)=-8239k^2-2055416k+20147664,
\quad\Delta_s(k)=k^2+4.
\]

They are squarefree and coprime. The existing commuting involutions exchange the two quadratic roots independently:

\[
\iota_x(x,y)=\left(\frac{333095x-432252}{212505x-333095},y\right),
\quad
\iota_y(x,y)=\left(x,-\frac{3y+5}{2y+3}\right).
\]

Their product negates both radicals. Therefore its invariant field is

\[
\mathbb Q(k,\sqrt{\Delta_x(k)\Delta_s(k)}).
\]

This gives an explicit genus-one quotient curve

\[
\boxed{C':\quad w^2=(k^2+4)(-8239k^2-2055416k+20147664).}
\tag{10}
\]

On the dense chart where the displayed functions are finite, its quotient map is

\[
\boxed{w=
\{2(310k-1860)x+732-579k\}\,(4y+6-k).}
\tag{11}
\]

Each factor squares to its associated discriminant, so (11) satisfies (10). The verification script checks the cleared identities exactly, reducing the only curve-dependent remainder to an explicit multiple of \(P(x,y)\).

The quotient has genus one because its right-hand quartic has four distinct roots. The degree-two map \(C\to C'\) is unramified: a fixed point of \(\iota_x\iota_y\) would require a common branch value of the two discriminants, and their gcd is one. Riemann–Hurwitz gives the same conclusion from the two genera. After choosing an origin over \(\mathbb C\), this involution is translation by a nonzero order-two point. The associated Jacobian homomorphism is the rational 2-isogeny above.

For a direct invariant check, the quartic of (10) is

\[
-8239k^4-2055416k^3+20114708k^2-8221664k+80590656,
\]

with

\[
I'=345936821751184=16(q^2-192R),
\]
\[
J'=-23357015742842360577664
=64\{-2q(q^2+576R)\}.
\]

Translate \(E'_0\) to short Weierstrass form and scale the coordinates by \(36,216\). The resulting coefficients are exactly \(-27I',-27J'\). This proves the claimed identification of \(\operatorname{Jac}(C')\) with \(E'_0\) over \(\mathbb Q\), including its rational twist class.

The field square therefore carries a full geometric chain:

\[
\boxed{\text{two quadratic sheet exchanges}
\ \longrightarrow\ C\longrightarrow C'
\ \longrightarrow\ E_0\overset{2}{\longrightarrow}E'_0.}
\]

## 4. Quadratic twisting preserves the usable structure

For any nonzero rational \(D_0\), the corresponding quadratic twist has the convenient model

\[
E_{0,D_0}:y^2=x^3+D_0q x^2-4D_0^2tR x.
\]

Its rational order-two point remains \((0,0)\), and its isogenous companion is

\[
E'_{0,D_0}:y'^2=x'^3-2D_0q x'^2
+D_0^2(q^2+16tR)x'.
\]

The same rational formula (4), with \(a_0=D_0q,b_0=-4D_0^2tR\), gives the isogeny. Hence any theorem whose hypotheses concern rational 2-isogenies or their quadratic twists has a concrete family on which to test its assumptions, local conditions and consequences. This is the point of contact with the repository's 2-primary BSD, Goldfeld and descent manuscripts; their exact theorem hypotheses and applicability are recorded in the companion source analysis.

## 5. Precision and reproduction record

All 18 checks in the current script use exact integers or exact multivariate polynomials. The generic identities are proved simultaneously in all seven coefficient variables. The original specialization includes factorization, discriminants, explicit quotient-map equations and the rational identification of both Jacobians. No floating precision is involved.

Run from the project root with the existing CPU environment:

```powershell
& 'work\exploration-lab-runtime\Scripts\python.exe' 'outputs\OpenAI-Math-Greater-Work\computations\verify_elliptic.py'
```

The script writes its complete [JSON record](../computations/elliptic-results.json). It starts no application and uses no GPU resources.

