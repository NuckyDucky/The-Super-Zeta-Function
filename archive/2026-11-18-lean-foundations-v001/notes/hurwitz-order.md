# The Hurwitz value is the derivative of the retained order contrast

16 November 2026. Exact Bernoulli identities, complex finite-level
stationarity and the first corrections toward the order-selected radius.

## 1. One polynomial bridge in the actual Cayley coordinate

Retain the normalized order-contrast polynomial and phase coordinate

\[
D(\kappa)=\frac{\kappa(\kappa-1)(\kappa-2)}{12},\qquad
q=\frac z{1+z},\qquad \kappa=2q.
\]

Write its Cayley form as

\[
\mathcal D(q):=D(2q)
=\frac{q(1-q)(1-2q)}3.
\tag{1}
\]

The two Bernoulli polynomials are

\[
B_2(q)=q^2-q+\frac16,\qquad
B_3(q)=q^3-\frac32q^2+\frac12q.
\]

The classical negative-integer Hurwitz formula is
zeta(-m,q)=-B_(m+1)(q)/(m+1), as in
[NIST DLMF 25.11.14](https://dlmf.nist.gov/25.11.E14).
Bernoulli reflection is B_m(1-q)=(-1)^m B_m(q), as in
[DLMF 24.4.3](https://dlmf.nist.gov/24.4.E3).
Consequently the exact bridge is

\[
\boxed{\mathcal D(q)=\frac23 B_3(q)=-2\zeta(-2,q),}
\tag{2}
\]
\[
\boxed{H(q):=\zeta(-1,1-q)=\zeta(-1,q)
=-\frac12B_2(q)
=-\frac1{12}+\frac q2-\frac{q^2}2,}
\tag{3}
\]
\[
\boxed{D'(2q)=B_2(q),\qquad
\mathcal D'(q)=-4H(q).}
\tag{4}
\]

Here the Hurwitz spectral arguments are fixed at -1 and -2; the
varying parameter is q. On the requested real-exponent powered-phase
paths, Re(z)>0 and therefore 0<Re(q)<1. Both q and 1-q are in the
right half-plane, fixing the usual Hurwitz continuation from its
defining series on its ordinary parameter domain. At these negative
integer arguments (2)-(4) are polynomial identities, so their displayed
values extend entirely in q. They retain no logarithmic ambiguity in q.

The source logarithm used to construct z is still the actual unwrapped
ell= sigma*t+i*tau*theta; this coordinate change does not change that
logarithm or its address.

## 2. The same zero is a residue value and an exact positive radius

For every finite normalized phase z!=-1, its iterative residue is

\[
\rho(q)=\frac{(2q-1)^2+1}{6}
=\frac{z^2+1}{3(1+z)^2}.
\]

Equations (3)-(4) give the exact complex identities

\[
\boxed{H(q)=\frac{1-3(2q-1)^2}{24}
=\frac{2-9\rho(q)}{12}
=-\frac{z^2-4z+1}{12(1+z)^2}.}
\tag{5}
\]

Thus the following conditions are equivalent, with their reciprocal
choices retained:

\[
\boxed{H(q)=0\quad\Longleftrightarrow\quad
\rho(q)=\frac29\quad\Longleftrightarrow\quad
q=\frac12\mp\frac1{2\sqrt3}\quad\Longleftrightarrow\quad
z=2\mp\sqrt3.}
\tag{6}
\]

On the outer positive resolved boundary 0<z<=1, the selected values are

\[
r_{\rm ord}=2-\sqrt3,\qquad
q_c=\frac{r_{\rm ord}}{1+r_{\rm ord}}
=\frac12-\frac1{2\sqrt3}.
\tag{7}
\]

This also follows directly by differentiating the contrast with respect
to its positive phase radius:

\[
\frac{d}{dz}\mathcal D\!\left(\frac z{1+z}\right)
=-\frac{4H(q)}{(1+z)^2}
=\frac{z^2-4z+1}{3(1+z)^4}.
\tag{8}
\]

The H zero is exactly the stationary point of that retained contrast,
and its residue is exactly 2/9. Reciprocal exchange q->1-q leaves
H and rho invariant while reversing the sign of mathcal D. Complex
conjugation conjugates all three values.

## 3. Exact finite-level stationarity along the complex powered phases

For one actual level put a=theta_n/t_n>0, retain both signs, and set

\[
b=\sigma+i\tau a,\qquad
z(c)=e^{-bc},\qquad
q(c)=\frac1{1+e^{bc}},\qquad 0<c\le t_n/4.
\tag{9}
\]

These are the full powered phases recovered as opposite-tag ratios of
the primary halfweight affix. Their path derivatives are

\[
q'=-bq(1-q),\qquad
\frac d{dc}\mathcal D(q(c))
=4bq(1-q)H(q).
\tag{10}
\]

**Proposition (finite-level Hurwitz stationarity).** For c>0 in the
requested window, mathcal D is nonzero and

\[
\boxed{\frac d{dc}|\mathcal D|^2
=8\Re\{bq(1-q)H(q)\overline{\mathcal D(q)}\},}
\tag{11}
\]
\[
\boxed{\frac d{dc}\log|\mathcal D|^2
=24\Re\!\left\{\frac{bH(q)}{1-2q}\right\}.}
\tag{12}
\]

Therefore every interior finite-level order maximum is characterized by

\[
\boxed{\Re\!\left\{\frac{(\sigma+i\tau a)H(q)}{1-2q}\right\}=0.}
\tag{13}
\]

Equivalently, using (5), it is the real projection of the exact residue
response b(2-9*rho)/(1-2q). All four tags give the same real equation,
by reciprocal and conjugate transport. The endpoint c=0 has
mathcal D=0 and is handled directly by the polynomial; the logarithmic
formula (12) is used only for c>0.

**Proof.** Differentiate (1) by (4) and use q' in (10). The product
rule for the squared modulus gives (11); dividing by its nonzero value
and cancelling q(1-q) gives (12). In the requested window,
0<a*c<pi/4, so Im(q) has sign -tau and is nonzero. Thus q is neither
0,1 nor 1/2, and the cancellation is valid. QED.

This equation agrees exactly with the finite contrast equation already
derived from the two exponential stages. Writing

\[
G(c,a)=\sinh c[2\cos(ac)-\cosh c]
+a\sin(ac)[2\cosh c-\cos(ac)],
\]

direct simplification gives the positive-factor identity

\[
\boxed{\Re\!\left\{\frac{bH(q)}{1-2q}\right\}
=\frac{G(c,a)}{12[\cosh^2c-\cos^2(ac)]}.}
\tag{14}
\]

The denominator is positive for c>0. The existing unique-max theorem
therefore transfers directly to the Hurwitz equation (13): endpoint
maxima for n<=34, and its unique interior zero for every n>=35.

At every finite interior optimum H(q) is nonzero. Its only polynomial
zeros in (6) are real, while the actual q in (9) has a nonzero imaginary
part. The precise stationarity condition is its projected complex
response (13). On the limiting real boundary a=0, b=sigma and the
condition reduces to H(q)=0, producing (6)-(7).

## 4. First finite-level corrections toward the common Hurwitz zero

Let

\[
c_0=\operatorname{arcosh}2=\log(2+\sqrt3),\qquad
d_2=c_0-\frac{c_0^2}{\sqrt3}.
\]

The simple limiting maximum and the implicit-function theorem give a
real even analytic maximum c(a)=c_0+d_2*a^2+O(a^4) near a=0.
At all sufficiently high actual levels, uniqueness identifies this
analytic branch with the finite-level selected maximum.

**Proposition (complex Cayley and Hurwitz corrections).** At that
maximum, for each of the four retained signs,

\[
\boxed{
q_{\sigma,\tau}(a)=\frac12-\frac{\sigma}{2\sqrt3}
-\frac{i\tau c_0}{6}a
+\sigma\left[-\frac{c_0}{6}
+\frac{c_0^2}{12\sqrt3}\right]a^2+O(a^3),}
\tag{15}
\]
\[
\boxed{H(q_{\sigma,\tau}(a))
=-\frac{i\sigma\tau c_0}{12\sqrt3}a
+\left[\frac{c_0^2}{36}-\frac{c_0}{12\sqrt3}\right]a^2
+O(a^3),}
\tag{16}
\]
\[
\boxed{\rho(q_{\sigma,\tau}(a))
=\frac29+\frac{i\sigma\tau c_0}{9\sqrt3}a
+\left[\frac{c_0}{9\sqrt3}-\frac{c_0^2}{27}\right]a^2
+O(a^3).}
\tag{17}
\]

The real parts are even analytic functions of a and the imaginary parts
are odd. In particular the real remainders after their displayed
quadratic terms are O(a^4), while the imaginary remainders are O(a^3).

**Derivation.** For the outer positive-angle tag, let Q(h)=1/(1+e^h).
At h=c_0, Q=q_c, Q'=-1/6 and Q''=1/(6*sqrt(3)). Expanding
h=(1+i*a)c(a) gives

\[
q=q_c-\frac{i c_0}{6}a
-\left[\frac{d_2}{6}+\frac{c_0^2}{12\sqrt3}\right]a^2
+O(a^3).
\]

Reciprocal/conjugate transport gives (15). Substituting it into the
exact quadratic H gives
H=-i*c_0*a/(12*sqrt(3))-d_2*a^2/(12*sqrt(3))+O(a^3),
which is (16). Equation (5) then gives (17).

The correction d_2 can also be recovered directly from the Hurwitz
stationarity equation. Write c(a)=c_0+d*a^2+O(a^4). Substitution in
the left side of (13) gives

\[
\Re\!\left\{\frac{(1+ia)H(q)}{1-2q}\right\}
=\frac{c_0-d-c_0^2/\sqrt3}{12}a^2+O(a^4).
\]

Its vanishing forces d=d_2, independently reproducing the correction
from the exponential-stage critical equation. Analyticity of c(a^2)
and Q supplies the stated remainder orders. QED.

Thus the finite complex Hurwitz values carry a signed imaginary approach
of order theta_n/t_n and a shared real correction of order
(theta_n/t_n)^2. Their limiting zero is the same exact point as the
real residue value 2/9 and the selected radius 2-sqrt(3).

## 5. Reproduction

`computations/verify_hurwitz_bridge.py` checks the Bernoulli, Hurwitz,
derivative and residue identities symbolically, independently derives
the small-a coefficients, and reconstructs selected actual finite-level
maxima with directed Arb/Acb arithmetic. It checks the Hurwitz special
functions directly against their polynomial values, all four tag
symmetries, the projected stationarity equation and its exact G factor,
and records the scaled correction remainders. The directed root brackets,
precision and selected values are retained in `hurwitz-bridge-results.json`.
