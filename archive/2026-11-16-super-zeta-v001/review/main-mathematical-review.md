# Independent mathematical review of the main Greater Work

16 November 2026. Reviewed `Greater-Work.md` against the seven companion
notes, their explicit formulas, numerical records and the independent
reviews retained in this package. This is a bounded integration review;
no new research direction or original artifact was introduced.

**Outcome: passed.** The substantive mathematical chain and numerical scopes
agree with the companion proofs. The following three local
wording/normalization clarifications were sent to the root agent, applied
to the current main synthesis, and independently confirmed before packaging:

1. Before (25), explicitly give the normalized branch weights
   \(\xi/4,\xi^{-1}/4,\upsilon/4,\upsilon^{-1}/4\), equivalently
   \(a=b=1/2\) in the companion \(\mathcal L_\epsilon\).
   The current statement also explicitly restricts the holomorphic
   supertrace to \(n\ge1\).
   Unnormalized step monomials would give the count
   \(\binom{2n}{n}^2\); the correct companion operators give the
   probability \(B_n^2\).
2. In Section 4, explicitly identify the Barnes asymptotic as
   \[
   \Gamma(N+1)\left[\frac{G(N+3/2)}{G(N+2)}\right]^2
   =N^{-1/4}(1+O(N^{-1})),
   \]
   leaving the factor \(G(3/2)^{-2}\) outside. This preserves the
   constant visibly in the proof of (B).
3. Immediately after (B), change “pole order” to “pole index.” The index
   \(n\) labels \(s=1/2-n\); every pole in the shifted theorem has
   order one.

## 1. Core coefficient identity and spectral conventions

In (A), the residue normalization is exactly \(B_n\), the lattice trace
is exactly \(B_n^2\), and the product-of-chords moment is exactly
\(B_n^2\). For the lattice operator in (22), each cardinal step has
weight \(1/4\). The bijection from two simultaneous signs to a cardinal
step is invertible; a length-\(2n\) return means zero total charge in
each sign stream. There are \(\binom{2n}{n}^2\) returning words out of
\(4^{2n}=16^n\), giving the stated probability and no extra factor two.

The original reciprocal lifts remain \(U=LQ\), \(V=-LP\), with
\(\alpha=U\). The determinant coordinate and quartet radii agree with
the frozen complete classification and exact radial-product theorem.
The inverse-cosine coupling has its explicit determinant and the
original reciprocal section is \(\varepsilon=1\).

## 2. Shifted superzeta and all residues

For \(\Re\varepsilon>0\), the negative spectral axis contains no
zero, since a zero there would force
\(\varepsilon^2=-v\operatorname{sech}^2\sqrt v\). Thus the stated
principal powers and real nonnegative shifts are compatible.

The Mellin strip \(1/2<\Re s<1\), large-endpoint expansion,
central-binomial residue signs and positive-integer endpoint
cancellations are correct. The complete shifted pole list is simple
at \(1/2-n\); nonpositive integer values vanish. The finite-part sign
at zero gives the determinant \(4E_\varepsilon(-w)\), agreeing with
the companion gamma–Bessel proof. Every positive-integer trace in (7)
has the correct derivative order and factorial.

## 3. Elliptic parameter, positive measure and modular branch

The complete elliptic integral uses its parameter, not modulus. The
hypergeometric series, ODE, Legendre period normalization \(1/\pi\),
arcsine moments and multiplicative chord density agree with the directly
checked formulas. The shorter-arc coverage model specifies a different
observable on the same explicit endpoint distribution; its expected
coverage and new contribution have the correct indexing.

The reciprocal AGM bounds are directed in the proper orientation:
\(1/a_j\le\mathcal M\le1/b_j\). The theta identity uses the nome
\(e^{\pi i\tau}\) and the branch continued from the positive imaginary
axis. These are the same conventions in `verify_residue_period.py`.
That script separates exact coefficients and coverage fractions, directed
AGM/analytic-tail statements, and high-precision theta/quadrature points.

## 4. Barnes constant and the deformed zeta at zero

The finite product (15), \(N^{1/4}\) normalization, exact constant
\(C_*=e^{\sin d/2}/G(3/2)^2\), strict tanh-kernel remainder and
the two finite-cutoff logarithmic terms all agree with the reviewed
binomial notes and directed results.

The renamed exponent \(\beta\) correctly distinguishes the
central-binomial deformation from the spectral shift \(w\).
The residue \(-\beta/4\), finite-part derivative \(\log C_*\),
and diagonal \(Z_\Lambda(s)=\mathfrak Z(s,-s)\) are correct.
Expanding \(s\zeta(s+1)/4\) gives its finite contribution \(+1/4\),
and the Euler constant cancels in the derivative. Therefore
\(Z_\Lambda(0)=-1/4\) and
\(\det_\zeta\Lambda=\sqrt{2\pi}C_*\), with the printed numerical value.

## 5. Actual inverse supertraces, quartet labels and clock time

The continuous character symbol recovers the actual retained phase
logarithms at \((\xi,\upsilon)=(\sigma,\tau)\). Its constant-term
exponential is exactly \(I_0(st_n)J_0(s\theta_n)\).
The geometric inverse branches themselves are evaluated at the fixed
Dottie parameter \(L_*\); the quartet index enters through the displayed
coefficient weights. The synthesis keeps those roles and the two grades
separate.

The four-branch disk, logarithmic sheets, derivative bound, separation
and invariant margins match the directed companion certificate. The
trace difference of functions and derivative-weighted compositions is
one for each ordered inverse word. With the normalized weights identified
above, its zero-charge projection is \(B_n^2\). The individual traces
retain the actual inverse fixed points and derivatives.

The cyclic clock uses the ordinary matrix trace. It multiplies a
time-\(j\) trace by \(m\mathbf1_{m\mid j}\). Thus at scalar time
\(2h\) the all-level coefficient depends on \(v_p(2h)\), exactly as
printed, rather than \(v_p(h)\). Each scalar inverse block represents
two physical half-steps, so this word has \(4h\) physical steps.
The coefficient in (26), the denominator \(l\) in (27), the logarithmic
germ convention, and the retained-level domain including \(\eta=1\)
agree with the companion definitions. The reported product tail bounds
the infinite truncation; its Bessel partial sum is labelled a point
evaluation.

## 6. Actual signed returns and primitive counts

The composition-operator order is the forward signed order. Primitive
balanced roots have repetition divisors of \(n\), yielding the factor
\(1/(2n)\) and the stated Möbius counts/Euler factors. The history zeta
variable counts half-length, while the transfer clock counts individual
scalar inverse blocks; these are explicitly distinguished.

The Schwarzian and logarithmic-derivative chain rules give the exact
finite phase formula (31). Cyclic origin changes scale \(S_1,S_2\)
by the correct powers, preserving the residue. The lifted action formula
has its actual integer branch and balanced-sign cancellation.

The \(++--\) certificate is for its own four-stage return at the
displayed \(y\). Its antiholomorphic half-return is
\(J\circ E_+^2\); the four phases and nonzero quadratic coefficient
are part of the directed certificate. The equal-count alternating word
uses the displayed Dottie parameter and is the second iterate of the
two-stage alternating return. Its residue is therefore \(\rho_D/2\),
with the printed positive value. The main comparison preserves both
actual maps and their parameters. The formal Fatou logarithmic
coefficient is correctly \(\rho_w\).

## 7. Laplace/Barnes hierarchy and Morse coefficient

The maximum of \(r(v)=v\operatorname{sech}^2\sqrt v\) occurs at
\(v=\nu^2\), where \(\nu\tanh\nu=1\). Expanding the logarithm
gives the factor \(1/(m\varepsilon^{2m})\) and the written convergence
condition. The coefficient integral converts under \(v=x^2\) to
\(2\int x^{2m-2s-1}\operatorname{sech}^{2m}x\,dx\), which gives
exactly \(2^{2s+1}\Gamma(2m-2s)\eta_{2m}(2m-2s,m)\).
The multiple-zeta definition, initial half-plane and degeneracy convention
match the finite eta reduction. The displayed tail follows from
\(r^{m-1}\le R_{\rm L}^{2m-2}\), with the correct power \(q^M\).

For \(g(x)=2\log x-2\log\cosh x\),
\[
g''(\nu)=-2/\nu^2-2\operatorname{sech}^2\nu=-2.
\]
The Laplace prefactor is therefore
\(2\sqrt\pi\,\nu^{-2s-1}R_{\rm L}^{2m}m^{-1/2}\), as written.
In a local Morse coordinate, \(r/R_{\rm L}^2=1-u^2\) and
\(dx/du=1\) at the saddle. The measure coefficient is
\(2\nu^{-2s-1}\). Multiplying it by
\(\int_{\mathbb R}\log(1+\delta/u^2)du=2\pi\sqrt\delta\)
gives precisely \(4\pi\nu^{-2s-1}\sqrt{1-X}\).
Odd amplitude terms cancel on a symmetric local interval, even higher
terms and the outside region contribute \(O(1-X)\). This verifies
the stated real-side expansion and chosen slit continuation.

## Source and evidence scope

The synthesis attributes the classical hypergeometric, AGM, theta,
Barnes, lattice and multiple-zeta formulas to their sources, while
identifying the exact reciprocal spectrum/phase input and the new
specializations. It keeps the Legendre period family separate from the
earlier fixed arithmetic curve, preserves all numerical precision labels,
and distinguishes exact algebra, directed certificates, analytic tails
and point computations. The companion analytic proofs support the
corresponding exact assertions throughout the synthesis.
