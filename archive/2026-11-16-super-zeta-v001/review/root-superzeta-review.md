# Independent review: shifted residues, chord periods, and the Laplace–Barnes hierarchy

16 November 2026. Reviewed `shifted-superzeta.md`,
`residue-period-and-chords.md`, and `laplace-barnes-expansion.md` in full.
The displayed shifted residues, determinant, Bessel continuation, chord
measure, modular identity, Barnes coefficients and coupling-tail bound pass
the proof review below. A proposed Laplace coefficient asymptotic and fold
law were also independently confirmed to the main author.

## Independent computational checks

The separate `computations/review_root_coefficients.py` uses mpmath at
90 decimal digits and integer polynomial arithmetic. Its result is
`computations/root-coefficient-review-results.json`.

- Thirteen Gamma-quotient residues, orders 0 through 12, agree with
  binom(2n,n)/(4^n pi) to better than 10^-80.
- For Barnes orders m=1,2,3,4, the polynomial degeneracy is checked at
  integer arguments, including its zeros below m. Sixteen independent
  coefficient integrals use s=-1/4,0,1/4,3/4, with a fourth-power
  endpoint substitution. Their finite Dirichlet-eta expressions agree
  to better than 2.75 x 10^-89.
- Two independent sixty-term Bessel-K tail sums at complex s and positive
  w lie within the written uniform tail bound. The omitted sums are
  approximately 8.1354 x 10^-5 and 2.6841 x 10^-5, with proved bounds
  2.3880 x 10^-4 and 6.2398 x 10^-5 respectively.

These are independent point checks. The root author's directed integrals
and branch certificates retain their separately specified numerical scope.

## Shifted-superzeta proof audit

The spectrum is the zero set of E_epsilon(lambda), including algebraic
multiplicities, and the shift is lambda+w with principal powers. Positive
real shifts preserve the stated negative-axis cut. The auxiliary coupling
is in Re(epsilon)>0; epsilon=1 remains the original reciprocal section.

The large-t logarithmic derivative is (t+w)^-1/2 plus an exponentially
small correction. Its binomial expansion has coefficient (-1)^n B_n w^n.
At s=1/2-n the Mellin sine factor equals (-1)^n, so the residue is exactly
B_n w^n/pi. Independently,

Gamma(1/2-n)=(-4)^n n! sqrt(pi)/(2n)!

makes the residue of Gamma(s-1/2)/(sqrt(pi)Gamma(s)) equal B_n/pi.
The residues are independent of epsilon. At w=0 all but the first vanish.
The nonpositive-integer values vanish because the shifted endpoint terms
are regular there after continuation, while the sine factor is zero.

The determinant identity is consistent with the canonical product and with
finite-part Mellin evaluation:

exp(-partial_s S(0,w;epsilon))=4E_epsilon(-w).

The large-T constant is -log4, and the lower endpoint contributes
-log E_epsilon(-w). This gives the displayed sign and factor four.
Shift differentiation gives (-1)^k(s)_k S(s+k,w), and the positive-integer
trace formula is the derivative of log E_epsilon(-w) with the stated sign.

The Bessel continuation has the correct multiplicity and normalization.
The reference spectrum is the full half-integer lattice, equivalently twice
the positive half-integer spectrum. Its Poisson heat sum has factor
1/sqrt(pi t), producing the Gamma term and the coefficient
4/(sqrt(pi)Gamma(s)) on the positive winding series. The relative shifted
Mellin derivative has derivative -F_epsilon(w) at s=0, as stated.

The K-tail bound is valid. For nu=s-1/2 and x>0,
|cosh(nu t)|<=cosh((Re(s)-1/2)t), while cosh(t)>=1+t²/2. Gaussian
integration gives a bound at least as strong as the one written in the
note. Multiplying by the winding prefactor gives exactly the stated
w^(-Re(s)/2) and m^(Re(s)-1) powers. The geometric denominator follows
from log(m/(M+1))<=(m-M-1)/(M+1). At nonpositive integer s the factor
1/Gamma(s) is interpreted by its entire continuation.

The residue order and quartet level are distinct indices. Their matched-n
normalization observable uses the actual two sequences explicitly, and
the note preserves this distinction.

## Elliptic/chord proof audit

The elliptic integral uses the parameter m, not the modulus k; therefore
the squared-residue transform is 2K(z)/pi and the square-lattice walk
resolvent in a per-step variable x is 2K(x²)/pi. The hypergeometric
coefficients and the stated differential equation agree.

For independent uniform endpoints on a circle, the endpoint-angle
difference is uniform. X=sin²(delta/2) has the stated arcsine density and
moments B_n. Multiplicative convolution of two independent copies gives

f_Z(x)=1/(pi² sqrt(x)) integral_x^1
[t(1-t)(t-x)]^-1/2 dt.

With t=x+(1-x)sin²(theta), the integral becomes 2K(1-x), exactly the
displayed density. Thus the positive measure, Stieltjes transform and
moments B_n² are all consistent.

The shorter arc has uniform normalized length on [0,1/2], mean 1/4.
Rotation invariance gives uncovered probability 3/4 at each fixed point;
independent chords and Fubini give 1-(3/4)^N expected coverage and
(1/4)(3/4)^(N-1) expected new coverage. This is the specified minor-arc
observable on the same explicitly defined endpoint model.

The series tail uses decreasing moments and a geometric sum. The AGM
normalization 1/AGM(1,sqrt(1-z)) and bracket 1/a_j <= M(z) <= 1/b_j
have the correct directions. The modular pullback uses the continued
period branch from the positive imaginary tau-axis, and
M(theta2^4/theta3^4)=theta3² has the stated parameter convention. Its
Fourier coefficients count two-square representations with the declared
q=exp(pi i tau).

## Laplace–Barnes coefficient audit

The maximum r(v)=v sech²sqrt(v) occurs at v=nu², nu tanh(nu)=1, and is
R_L². On |epsilon|>R_L, the logarithm's power series is uniformly inside
its disk of convergence along the whole positive ray. For Re(s)<1 the
integrable first coefficient dominates all further coefficients, justifying
the sum/integral interchange.

After v=x²,

I_m(s)=2 integral_0^infinity x^(2m-2s-1) sech^(2m)(x) dx.

Expanding sech^(2m) first in the absolutely convergent half-plane gives
the exact factor 2^(2s+1)Gamma(2m-2s) eta_(2m)(2m-2s,m). The power of
two and Gamma argument are correct. The finite reduction follows from
P_m(n)=n product_(j=1)^(m-1)(n²-j²) and
(-1)^(n-m)=(-1)^(m+1)(-1)^(n-1). This yields precisely the displayed
(-1)^(m+1)/(2m-1)! factor, including
I_2(s) proportional to eta(3-2s)-eta(1-2s).

The cited Hu–Kim definition was checked directly in its primary paper:
the multiple alternating sum has the same normalization used here.

The estimate I_m(Re(s))<=R_L^(2m-2) I_1(Re(s)) gives exactly
q^M/[(M+1)(1-q)] after M terms, with the displayed I_1/|epsilon|²
and |s sin(pi s)/pi| prefactors. The original epsilon=1 coupling lies
inside this convergent inverse-coupling expansion.

## Confirmed coefficient asymptotic and fold normalization

For g(x)=log[x² sech²x], at nu tanh(nu)=1 one has

g''(nu)=-2/nu²-2sech²nu=-2.

Since I_m(s)=2 integral x^(-2s-1)exp(mg(x))dx, ordinary Laplace
asymptotics give, uniformly on compact s-sets,

I_m(s) ~ 2sqrt(pi) nu^(-2s-1) R_L^(2m)/sqrt(m).

The coefficient constant is therefore correct. It gives the exact
inverse-coupling radius R_L^-2 for the nonzero logarithmic coefficient
hierarchy; in particular it applies to the s=0 curvature integral.
The uniform-logarithm threshold is retained as that explicitly stated
scope. At the trivial zeros of J, its vanishing prefactor is part of the
specialized analytic function.

The proposed branch coefficient is also correct. Put X=-R_L²/epsilon²
and F_s(X)=integral v^(-s-1)log(1-Xr(v)/R_L²)dv. An analytic local
Morse coordinate gives r(x²)/R_L²=1-u² near x=nu. The even amplitude at
u=0 is 2nu^(-2s-1). The elementary integral
integral_R log(1+delta/u²)du=2pi sqrt(delta) gives

F_s(X)-F_s(1) ~ 4pi nu^(-2s-1)sqrt(1-X).

A symmetric local u-domain makes the remaining even-amplitude terms
O(1-X); the exterior contribution is analytic. The positive square root
applies for real X increasing to one. A chosen slit-neighborhood branch
gives the corresponding complex continuation. This confirms the fold
constant independently of the Barnes reduction.

No principal formula correction was needed. The convergence-radius scope
and the reciprocal-Gamma convention were communicated as precision-of-
statement points to the main author. All review work was headless CPU
analysis in this new output folder.
