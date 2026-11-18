# Independent review: the original quartic is locally soluble and globally pointless

**16 November 2026.** I independently checked the new proof in `research/hasse-obstruction.md`, the explicit map and polynomial identity, the complete local-prime coverage, all rational exceptional cases, and the squareclass image argument. I replayed the updated exact arithmetic plus hidden GP calculation in approximately **0.095 seconds**. The theorem passes this review.

The conclusion is

\[
C(\mathbf R)\ne\varnothing,\qquad C(\mathbf Q_p)\ne\varnothing\ (\text{all }p),
\qquad C(\mathbf Q)=\varnothing,
\]

for the user's original smooth projective quartic

\[
C:Y^2=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\]

## 1. Exact covering identity and target curve

Write q=5028677, B=−305545084240=−16R, R=19096567765. The target is the already verified Jacobian

\[
E:z^2=X^3+qX^2+BX.
\]

The retained K is quadratic, M is quartic, and f_h is the homogeneous quartic. The script verifies the degree-eight homogeneous identity, by dehomogenization and exact polynomial coefficients,

\[
-16K^4+4qK^2f_h-Bf_h^2=4M^2.
\]

Consequently substituting X=−4K²/Y² gives

\[
X^3+qX^2+BX
=\frac{4K^2}{f_h^3}(-16K^4+4qK^2f_h-Bf_h^2)
=\left(\frac{4KM}{Y^3}\right)^2.
\]

The sign and scaling of every term agree with the explicit target E. This direct identity supplies the needed map independently of any convention for Hessian covariants.

The covering map C->E has degree **four**: X=−4K²/f_h is degree four as a rational function of the base coordinate, and each curve's abscissa has degree two. It is a 2-cover in the usual genus-one descent terminology. The separate x-projection C->P1 has degree **two**. The report's proof uses these maps consistently.

## 2. All rational exceptional cases

The norm representation f_h=(N_h−D_h)²+4N_h² and nonzero resultant show f_h>0 at every nonzero real projective pair. Thus a rational C point has Y!=0. The covering formulas are homogeneous of weight zero under (x,v,Y)->(lambda*x,lambda*v,lambda²Y), so they apply to every rational projective base coordinate, including infinity, whenever a C point is rational.

The quadratic K has discriminant 4R. Since R is nonsquare, K has no nonzero rational projective zero. Hence the resulting target point has X!=0 and cannot be O or (0,0). It satisfies

\[
[X]=[-1]\in\mathbf Q^*/\mathbf Q^{*2}.
\]

There is therefore no rational exceptional fiber that escapes the squareclass argument. At the two geometric points over infinity, Y²=961000=310²*10; they are themselves irrational over Q, which is also consistent with this check.

## 3. The global squareclass obstruction

For E:y²=x³+qx²+Bx, the standard rational 2-isogeny descent homomorphism alpha has values

    alpha(O)=1, alpha((0,0))=[B], alpha((X,z))=[X] for X!=0.

Its group property follows directly from the line/cubic intersection identity. For a line z=mX+n with nonzero intercept, the product of the three abscissae is n². For a line through (0,0), the product of the other two abscissae is B. These give both the generic group law and the exceptional torsion value. Vertical and tangent cases give the same squareclass identity.

Since its target has exponent two, alpha kills 2E(Q). The independently reviewed rank-one and torsion-two calculation gives

\[
|E(\mathbf Q)/2E(\mathbf Q)|=4,
\quad |\alpha(E(\mathbf Q))|\le4.
\]

The exact point P has x(P)=115*(28450240/954687)², so alpha(P)=[115]. The torsion point T has alpha(T)=[B]=[−R]. These two classes are independent: [115] is positive nonsquare and [−R] is negative. Therefore they already give the complete four-element image

\[
\alpha(E(\mathbf Q))=
\{[1],[115],[−19096567765],[−166057111]\}.
\]

The only negative representatives are −R and −R/115. Neither is equivalent to −1 because R and R/115 are nonsquares. The class [−1] required by the covering is absent, proving C(Q)=empty.

This argument uses the explicit P only modulo two. It needs the rank-one upper bound and full torsion structure, and it remains valid regardless of the saturation index of P in the free rank-one group.

## 4. Local solubility at every place

The exact discriminant factors into precisely the primes

    2,5,11,23,31,41,457,486971,1414835497.

The replay verifies a primitive rational projective pair (u,v) at each listed prime for which f_h(u,v) is a Qp square. Its square test uses exact valuation parity and the odd-prime unit residue or the 2-adic residue modulo eight. Those criteria establish a local point directly. The witnesses retained in `original-quartic-local.json` are:

|p|(u,v)|f_h(u,v)|
|---:|---|---:|
|2|(1,1)|568580|
|5|(1,5)|1164658100|
|11|(1,1)|568580|
|23|(0,1)|1813853|
|31|(1,0)|961000|
|41|(1,0)|961000|
|457|(1,1)|568580|
|486971|(1,1)|568580|
|1414835497|(2,1)|2917781|

At every other prime p, the characteristic is odd and the discriminant is a unit. The smooth proper genus-one reduction has at least p+1−2sqrt(p)>0 points by Hasse's bound; smooth Hensel lifting supplies a Qp point. This covers all remaining finite places. The positive norm form supplies real points. Thus the local part is complete.

## 5. Identification as a nonzero two-torsion Sha class

The exact binary-quartic Jacobian calculation identifies Jac(C) with E over Q. Local solubility places its genus-one torsor class in Sha(E/Q). The rational degree-two projection supplies a rational divisor of degree two, so 2[C]=0. Global pointlessness makes [C] nonzero. Together with the separately reviewed full descent,

\[
\boxed{0\ne[C]\in\Sha(E/\mathbf Q)[2]
\cong(\mathbf Z/2\mathbf Z)^2.}
\]

The local witnesses, map, squareclass checks and finite-field point counts use exact arithmetic. The upper rank bound and Cassels-pairing dimensions use the recorded PARI implementation. The original quartic's Hasse-principle failure follows from these classical descent computations independently of the repository's new theorem manuscripts.

## Review disposition

The explicit map, its degree and normalization, all rational exceptional fibers, the rank-to-squareclass cardinality argument, the complete local coverage and the nonzero Sha class are valid. The updated verification replay passed. This finding is ready to lead the research handoff as a concrete arithmetic property of the user's original coefficient curve.
