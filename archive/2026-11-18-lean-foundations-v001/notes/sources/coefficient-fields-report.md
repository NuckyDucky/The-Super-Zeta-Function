# The coefficient lattice, field diamond, and new polynomial minima

## 1. Reconstruction and preserved results

The original expression uses

\[
N(x)=-659-183x+465x^2,\quad D(x)=-936+396x+155x^2,
\quad F(y)=\frac{y^2+3y+2}{y^2+y-1}.
\]

The earlier certificates are retained in their original directories. Their recorded outcomes are reused here: the original ratio error is 2.62314394304443994766...e-20; its primitive coefficient sign class is the unique optimum at height936 and remains optimal through1203; the first improvement occurs at1204. The earlier frontier contains80 records through10^8, and the large coefficient-box certificates reach reconstructed-pi error5.0941084569009...e-1003. The associated reproduction logs report successful exact certificates and independent direct evaluations.

The present experiments address a new objective: minimum absolute polynomial value at (e,pi). The structured ratio and polynomial objectives are connected explicitly below.

## 2. The exact nine-monomial expansion

For v=(a,b,c,d,f,g), write n_i=(a,b,c)_i and d_i=(d,f,g)_i. Then

\[
P_v(x,y)=\sum_{i=0}^2x^i\left[
(-n_i-2d_i)+(n_i-3d_i)y+(n_i-d_i)y^2\right].
\]

For the original vector,

\[
\boxed{
\begin{aligned}
P(x,y)={}&2531+2149y+277y^2\\
&-609x-1371xy-579xy^2\\
&-775x^2+310x^2y^2.
\end{aligned}}
\]

The coefficient matrix, with rows indexed by powers of x and columns by powers of y, is

\[
\begin{pmatrix}
2531&2149&277\\
-609&-1371&-579\\
-775&0&310
\end{pmatrix}.
\]

The previously evaluated residual is P(e,pi)=4.05100411692257040693...e-16. Exactly,

\[
P_v(e,\pi)=(\pi^2+\pi-1)D_v(e)[R_v(e)-F(\pi)].
\]

Thus polynomial residual, denominator size, and ratio error can be compared using their actual scale factors.

## 3. The structured coefficient lattice is saturated of rank six

Each row is the image of the two integer parameters (n,d) under

\[
C=\begin{pmatrix}-1&-2\\1&-3\\1&-1\end{pmatrix}.
\]

Its column cross product is (2,-3,5). Consequently each image row (c0,c1,c2) satisfies

\[
\boxed{2c_0-3c_1+5c_2=0.}
\]

Conversely, this integer equation gives c1 congruent to c2 modulo2, so

\[
d=(c_2-c_1)/2,\qquad n=(3c_2-c_1)/2
\]

are integers and reconstruct the row. This proves that the lattice is the full integer plane cut out by that primitive normal. Three independent row blocks give a saturated rank-six sublattice of Z^9.

The block Gram matrix is

\[
C^TC=\begin{pmatrix}3&-2\\-2&14\end{pmatrix},\qquad
\det(C^TC)=38.
\]

The rank-six lattice therefore has covolume 38^(3/2) in its real span. The exact height transfers are

\[
H(P_v)\le4H(v),\qquad H(v)\le2H(P_v).
\]

The free bidegree(2,2) polynomial family has nine coefficient directions; Nick's structured family has six. These ranks are the relevant dimensions for the polynomial searches.

## 4. The exact field diamond

Put k=K(e)=4N(e)/(N(e)-D(e)) and s=2*pi_hat+3. The parameter k is transcendental because it is a nonconstant rational function of the transcendental number e.

Over the rational function field Q(k), e satisfies

\[
(310k-1860)e^2+(732-579k)e+(277k+2636)=0.
\]

Its discriminant is

\[
\Delta_e(k)=-8239k^2-2055416k+20147664.
\]

The reconstructed coordinate satisfies s^2-ks-1=0, with discriminant

\[
\Delta_s(k)=k^2+4.
\]

Both discriminants are squarefree, and their gcd is1. Their distinct simple roots show that their square classes are independent in Q(k)^*/Q(k)^(2). Therefore

\[
\boxed{
[\mathbb Q(e):\mathbb Q(k)]=
[\mathbb Q(\widehat\pi):\mathbb Q(k)]=2,
}
\]

\[
\boxed{\mathbb Q(e)\cap\mathbb Q(\widehat\pi)=\mathbb Q(k),}
\]

and

\[
\boxed{[\mathbb Q(e,\widehat\pi):\mathbb Q(k)]=4.}
\]

The top extension is Galois with group C2 x C2. Both upper edges of the diamond also have degree2. All these fields have transcendence degree1 over Q.

The two commuting involutions are the previously derived rational partner maps

\[
e\longmapsto\frac{333095e-432252}{212505e-333095},\qquad
\widehat\pi\longmapsto-\frac{3\widehat\pi+5}{2\widehat\pi+3}.
\]

They fix k and realize the two independent quadratic conjugations.

**The curve model.** Regarding P(x,y)=0 as quadratic in y and completing the square gives

\[
Y^2=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\]

The quartic is squarefree. The smooth projective model is a degree-two cover of the x-line with four simple branch points; Riemann–Hurwitz gives genus1. The field diamond describes this same function field through its common k-coordinate.

**Connection to the true pi.** Adjoining pi to the top field yields a finite extension of both Q(e,pi) and Q(pi_hat,pi). Preservation of transcendence degree under finite extensions proves

\[
\boxed{
\operatorname{trdeg}_{\mathbb Q}\mathbb Q(e,\pi)
=\operatorname{trdeg}_{\mathbb Q}\mathbb Q(\widehat\pi,\pi).
}
\]

In particular, algebraic independence of e and pi is equivalent to algebraic independence of pi_hat and pi. Under Schanuel, both pairs are algebraically independent and the small difference pi-pi_hat is transcendental. The Ax report derives the required Schanuel consequence from1 and i*pi. This separates the proved finite-field structure from its explicitly conditional arithmetic consequence.

## 5. Why six coefficient directions suggest sixth-power ratio accuracy

For d real numbers X_1,...,X_d, consider the (H+1)^d values q dot X with q_i in{0,...,H}. They lie in an interval of length at most H*sum(abs(X_i)). If two coincide, their difference gives an exact relation. Otherwise adjacent values give a nonzero integer vector v with maximum coefficient at most H satisfying

\[
\boxed{|v\cdot X|\le
\frac{H\sum_i|X_i|}{(H+1)^d-1}.}
\]

This is a direct pigeonhole bound with residual scale H^(-(d-1)). For the structured family d=6, the linear residual is N-TD. Along coefficient sequences with |D|>=cH and residual <=C H^(-5), the exact quotient relation gives ratio error <=(C/c)H^(-6). This identifies both sources of the sixth power: five powers from cancellation among six coefficient directions, and one from the denominator scale.

For a free nine-monomial polynomial family, the corresponding residual scale is H^(-8). The numerical experiments below compare these different objectives and dimensions using their declared coefficient boxes.

There is a useful rigorous metric result here. The analytic map

\[
(x,y)\longmapsto(x,x^2,F(y),xF(y),x^2F(y))
\]

is nondegenerate. Taking the five columns f_x,f_xx,f_y,f_xy,f_xxy gives determinant

\[
4F'(y)^3=
-\frac{4(2y^2+6y+5)^3}{(y^2+y-1)^6},
\]

which is nonzero throughout its real domain. Kleinbock–Margulis extremality therefore yields the usual dual exponent5 for almost every parameter pair on this manifold. Explicitly, for every epsilon>0 and almost every (x,y), there is c_epsilon>0 such that every nonzero integer coefficient vector of height H satisfies

\[
|N_v(x)-F(y)D_v(x)|\ge c_\epsilon H^{-5-\epsilon}.
\]

Using |D_v(x)|<=H(1+|x|+x^2) gives the corresponding ratio lower bound of order H^(-6-epsilon). [Kleinbock and Margulis, original paper](https://people.brandeis.edu/~kleinboc/Pub/flda.pdf), [1998 publication record](https://annals.math.princeton.edu/articles/12997).

The metric theorem has an almost-everywhere parameter quantifier. For the particular pair(e,pi), this project supplies exact finite coefficient-box minima and the earlier constructive continued-fraction family with its proved H^(-2) reconstructed-pi bound. The coefficient records and broad-height examples supply the measured sixth-power behavior.

The new diagnostic of the preserved80-record frontier finds D/H between0.2929121987094... and5.7263036215335.... Its endpoint error secant from height936 to the final height76079191 is6.30218460888567.... These are descriptors of the actual saved records. The signed residuals, primitive-seed minor gcd1, and uniform continued-fraction height constant1.79187477742317...e-14 are also recorded in experiments/frontier-diagnostics.json.

## 6. New globally certified polynomial experiments

The new search evaluates the following families:

- Free bidegrees(1,0),(2,0),(1,1),(2,1),(2,2).
- The original rank-six structured family, minimizing absolute P_v(e,pi).
- Exchange-symmetric bidegree(2,2), with six orbit coefficients.
- Simultaneously reciprocal bidegree(2,2), with five orbit coefficients.
- At most three nonzero monomials among the nine bidegree(2,2) monomials.

There are54 main coefficient-box minima,16 small-box control minima, and168 support-specific sparse certificates. Every completed minimum uses exact integer/rational enumeration and rigorous Arb interval comparisons. The main precision is2048 bits; direct scores use fresh constants at4096 bits. The separate peer audit uses8192-bit constants and independently re-enumerates the highest dense box with a different embedding scale and LLL delta.

The complete coefficients and certificates appear in experiments/polynomial-minima.json, polynomial-controls.json, and sparse-minima.json. Rows of a free polynomial vector follow the order1,pi,pi^2,e,e*pi,e*pi^2,e^2,e^2*pi,e^2*pi^2.

Selected exact minima for the free bidegree(2,2) family are:

| Coefficient bound H | Minimum absolute polynomial value, rounded |
|---:|---:|
|10|6.693603929e-9|
|100|4.212838523e-18|
|936|3.679629986e-25|
|10^4|3.746098124e-33|
|10^6|3.711385786e-49|
|10^9|7.542097574e-74|
|10^50|3.621018198e-401|

For example, the H=936 winner is

\[
\begin{aligned}
Q(x,y)={}&85-206y-690y^2\\
&+851x+213xy-282xy^2\\
&-297x^2+626x^2y-21x^2y^2.
\end{aligned}
\]

Every nonzero integer polynomial of bidegree at most(2,2) and coefficient height at most10^50 has absolute value at(e,pi) at least the positive minimum enclosed in the corresponding certificate. Its attaining polynomial is saved in full.

At structured vector height936, the new absolute-residual optimum is again the original six-integer sign class. At height10000, the residual optimum differs from the earlier ratio optimum, reflecting the explicit denominator factor in section2. The structured vector box bounds the six parameters v; the free box bounds the nine polynomial coefficients directly. The height-transfer formulas in section3 specify their comparison.

The sparse controls give minima8.14012326997e-9 at H936 and3.47009700752e-9 at H10000. All84 triples of possible monomial positions were certified at each height; this covers every polynomial with support at most3.

## 7. How the certificate works

For the chosen real basis X, choose exact integers q_i by rigorously rounding M X_i. The graph lattice is

\[
\Lambda=\{(v,q\cdot v):v\in\mathbb Z^d\}.
\]

Let E be a strict upper error cap obtained from a candidate. Any improving coefficient vector in the H-box satisfies

\[
|q\cdot v|\le ME+H\sum_i|q_i-MX_i|=:K_0.
\]

Thus all improvements lie in a finite lattice ball with squared radius dH^2+ceil(K_0)^2. The code verifies the reduced basis has determinant +/-1 in its first d columns and exactly the required q dot v in its last column. Exact Fraction Gram–Schmidt enumeration visits every lattice point in that ball. Primitive sign representatives suffice because division by an integer gcd reduces the absolute value while preserving the coefficient bound. Certified intervals strictly order the winner and all competitors in the ball.

At H=10^50, the independent dense-family enumeration used a different scale and delta=.99 and visited271223 lattice points. It found the same polynomial and error. Its record is ax-functional/root-peer-review.json.

The small-box controls additionally enumerate all coefficient vectors directly, including the nine-variable box H=2. The controls agree with the lattice certificates.

## 8. Relation to transcendence measures

Schanuel would give positivity of every nonzero P(e,pi). A quantitative algebraic-independence measure gives an explicit lower bound depending uniformly on degree and height. These are the arithmetic objects compared by the research program.

The classical report supplies two successful nearby settings: an explicit Hermite lower bound for e-only polynomials, and an algebraic-unit norm lower bound for integer-parameter Fibonacci roots. It also records Nesterenko's quantitative modular triples and the November2026 E-function measure. Those theorems provide concrete models for auxiliary-function design, arithmetic coefficient control, and zero estimates.

A further exact bridge transfers the Hermite bound to pi_hat itself. For nonzero integer p(Y) of degree at most d and height at most H, eliminate Y with the original curve using a resultant. The resulting integer polynomial in e has degree at most2d and height at most8601^d((d+1)H)^2. Its norm identity gives the explicit pi_hat lower bound proved in classical-theory-report.md section8A. This is a quantitative application to the actual reconstructed constant.

The current numerical certificate supplies a positive, sharp lower bound for each declared finite box at the actual point(e,pi). The exact field diamond, the functional Ax applications, and the restricted quantitative controls are independent proved components available for further work.
