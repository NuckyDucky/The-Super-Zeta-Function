# The original meme quartic is a Hasse-principle counterexample

**Computer-assisted arithmetic theorem, 16 November 2026.**

Nick's original six coefficients determine the genus-one curve

\[
C:\quad Y^2=f(x),
\qquad
f=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\]

This curve has points over the real numbers and over every p-adic field, and it has no rational point:

\[
\boxed{C(\mathbf R)\ne\varnothing,\quad
C(\mathbf Q_p)\ne\varnothing\text{ for every prime }p,\quad
C(\mathbf Q)=\varnothing.}
\tag{1}
\]

Its torsor is a **nonzero element** of

\[
\Sha(E/\mathbf Q)[2^\infty]\cong(\mathbf Z/2\mathbf Z)^2,
\quad
E:\quad z^2=X^3+5028677X^2-305545084240X.
\tag{2}
\]

The local solubility, explicit covering map, point and squareclass checks below use exact integer arithmetic. The rank-one upper bound and two-primary Sha structure use the reproducible PARI/GP 2-descent and Cassels-pairing computation in [arithmetic.md](arithmetic.md), with an independent review in [arithmetic-review.md](../review/arithmetic-review.md). The theorem (1) follows from classical descent and that calculation.

## Proof

Put

\[
q=5028677,\quad B=-305545084240=-16R,\quad
R=19096567765.
\]

The norm form is

\[
f=(N-D)^2+4N^2,\quad
N=465x^2-183x-659,\quad D=155x^2+396x-936.
\]

The resultant of \(N,D\) is \(R\ne0\), so this form is positive on the real projective line. In particular \(C(\mathbf R)\ne\varnothing\), and a rational point would have \(Y\ne0\).

The exact discriminant of \(f\) is

\[
2^8\cdot5^2\cdot11^2\cdot23^2\cdot31^2
\cdot41\cdot457\cdot1414835497\cdot486971^2.
\]

At each bad prime, an exact local-square witness is recorded in [original-quartic-local.json](../computation/original-quartic-local.json). For example, at 2, \(f(1)=568580=4\cdot142145\), and \(142145\equiv1\bmod8\). The table of all witnesses is in [arithmetic.md](arithmetic.md). At every remaining finite prime, the smooth genus-one reduction has a point by Hasse's bound and it lifts by Hensel's lemma. This proves the two local assertions of (1).

The global assertion follows from an explicit map. Define the homogeneous forms

\[
K(x,v)=212505x^2-666190xv+432252v^2,
\]

\[
\begin{aligned}
M(x,v)={}&529733615650x^4-1561869979515x^3v\\
&+879427559295x^2v^2+1338999985416xv^3
-1347558035330v^4.
\end{aligned}
\]

Writing \(f_h(x,v)\) for the homogeneous quartic, exact multiplication gives

\[
\boxed{-16K^4+4qK^2f_h-Bf_h^2=4M^2.}
\tag{3}
\]

Therefore any point \(Y^2=f_h(x,v)\) with \(Y\ne0\) gives a point on \(E\) through

\[
\boxed{X=-\frac{4K(x,v)^2}{Y^2},\qquad
z=\frac{4K(x,v)M(x,v)}{Y^3}.}
\tag{4}
\]

Indeed, substituting \(X\) into the right side of (2) factors it as
\[
\frac{4K^2}{f_h^3}
\bigl(-16K^4+4qK^2f_h-Bf_h^2\bigr)
=\frac{16K^2M^2}{Y^6}=z^2.
\]

The quadratic form \(K\) has discriminant

\[
666190^2-4\cdot212505\cdot432252
=4R=76386271060.
\]

Since \(R=5\cdot11\cdot23\cdot31\cdot486971\) is squarefree, \(K\) has no nonzero rational projective zero. Thus a rational point of \(C\) would give a point of \(E(\mathbf Q)\) with

\[
X=-(2K/Y)^2\ne0,
\qquad [X]=[-1]\in\mathbf Q^\times/\mathbf Q^{\times2}.
\tag{5}
\]

Now use the rational 2-isogeny descent homomorphism

\[
\alpha:E(\mathbf Q)\longrightarrow
\mathbf Q^\times/\mathbf Q^{\times2},\quad
\alpha(O)=1,\quad\alpha((0,0))=[B],\quad
\alpha((X,z))=[X]\ (X\ne0).
\]

Its homomorphism property can be read directly from the chord construction: a line \(z=mX+n\) meeting the cubic in three nonzero abscissae gives a cubic with constant term \(-n^2\), so the product of those abscissae is \(n^2\). A line through \((0,0)\) gives the exceptional value \(B\). Tangent cases give the same identity.

The arithmetic certificate establishes rank one and torsion group \(\mathbf Z/2\mathbf Z\). Hence

\[
\#E(\mathbf Q)/2E(\mathbf Q)=4,
\quad |\alpha(E(\mathbf Q))|\le4.
\]

For \(T=(0,0)\), \(\alpha(T)=[-R]\). The exact infinite-order point

\[
P=\left(
\frac{93082857946624000}{911427267969},
\frac{129969110503209045907820800}{870127764175520703}
\right)
\]

has

\[
X(P)=115\left(\frac{28450240}{954687}\right)^2.
\]

The classes \([115]\) and \([-R]\) are independent: one is positive nonsquare, the other negative. They already generate four classes, so

\[
\boxed{\alpha(E(\mathbf Q))
=\{[1],[115],[-19096567765],[-166057111]\}.}
\tag{6}
\]

Here the last representative uses \(R/115=166057111\); it represents the product of the two generators. Neither \(R\) nor \(R/115\) is a square. Consequently \([-1]\) is absent from (6), contradicting (5). Therefore \(C(\mathbf Q)=\varnothing\).

Finally, the rational degree-two x-projection gives \(2[C]=0\). Local solubility puts \([C]\) in \(\Sha(E)[2]\), and global pointlessness makes this class nonzero. The group structure in (2) follows from the full 2-descent described in the arithmetic companion. This completes the proof.

## Computational record

[verify_arithmetic.py](../computation/verify_arithmetic.py) verifies the polynomial identity (3), the discriminants, the exact rational point, its squareclass, the local witnesses and all elementary group inputs. With its optional GP argument it replays the complete rank and Cassels-pairing computation:

    python computation/verify_arithmetic.py --gp /absolute/path/to/gp

The final exact record is [arithmetic-results.json](../computation/arithmetic-results.json). Its original-quartic section records the nonzero torsor class and empty rational-point set, using the rank-one certificate.

The covering map can also be recovered from the classical binary-quartic Hessian. At the rational root \(\varphi=-q\) of \(X^3-3IX+J\), Fisher's cubic invariant has value \(-722534000400=-(850020)^2\), while his singular Hessian combination is \(-16K^2\). The explicit identity (3) supplies a direct coordinate verification of the normalization. See [Fisher (2022), §§2–3 and equation (14)](https://link.springer.com/article/10.1007/s40993-022-00376-z).
