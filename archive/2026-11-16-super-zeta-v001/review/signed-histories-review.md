# Independent review of ordered signed histories

16 November 2026. Reviewed `research/ordered-signed-histories.md` and
`computations/verify_signed_histories.py`; independently replayed the complete
verifier.

**Outcome:** the primitive counts and Euler factors, normalized elliptic
derivative and critical value, lifted phase action, Schwarzian residue
formula, actual four-stage return and its three-variable existence/uniqueness
certificate are correct. The verifier passed in approximately **0.164 seconds**.

## Ordered operators and primitive factors

For \(C_s f=f\circ E_s\), the operator product
\(C_{s_1}\cdots C_{s_m}\) acts by the stated forward composition
\(f\circ E_{s_m}\circ\cdots\circ E_{s_1}\). Thus the constant-term
projection retains order, and its first commutator at zero is correctly
\(e^{-L}-e^L\).

A proper repetition of a balanced word has a balanced primitive root and a
repetition divisor of \(n\), rather than an arbitrary divisor of \(2n\).
Each primitive root of length \(2k\) has \(2k\) marked origins. This
proves the count, the factor \(1/(2n)\), and the primitive Euler product
with the variable marking half-length. The same argument holds under
simultaneous rotation of two streams. The complementary-half condition
allows precisely the odd repetition divisors, giving the separate formula
in Section 6. The direct enumerations in the script independently check
these conventions.

The parameter-convention elliptic series gives
\(t\partial_t\log\widehat{\mathcal Z}_2=\mathbf K(t)/\pi-1/2\).
The torus logarithm has exactly the factor \(1/(2n)\) because its odd
moments vanish and its \(2n\)-th moment is \(B_n^2\). Integrating one
angle gives \(\log[(1+|\sin\theta|)/2]\); the displayed log-sine
integral then gives \(4e^{-4G_{\rm Cat}/\pi}\). The critical logarithmic
singularities are integrable. The induction
\(B_n^2\le1/(3n+1)\) correctly proves the retained positive-series tail
bound \(1/(6N)\).

## Phase formulas and cyclic invariance

Multiplying the actual derivatives and exponential lifts gives
\(\mu=L^m(\prod s_k)e^{\mathcal A_w}\). At balanced length \(2n\)
and \(L=iy\), both signs cancel to yield \(y^{2n}e^{\mathcal A_w}\).
The lifted integer and action are invariant under a simultaneous cyclic
rotation of signs and stage phases.

The chain rule gives
\(F''/F'=L\sum s_{j+1}D_j\). Since each signed exponential has
Schwarzian \(-L^2/2\), the composite has
\(-L^2\sum D_j^2/2\). At multiplier one these identities give exactly
\[
a_w=LS_1/2,
\qquad \rho_w=S_2/(3S_1^2).
\]
Under a cyclic origin change, the two sums acquire factors \(D_j^{-1}\)
and \(D_j^{-2}\), proving invariance of their quotient. The alternating
two-stage specialization correctly reproduces the Dottie residue.

## The actual four-stage certificate

Let \(A=E_+^2\), \(H=J\circ A\). The forward word \((++--)\) has
return \(H^2\). Solving \(A(z)=\bar z\) and \(|A'(z)|=1\) therefore
produces a fixed point of the stated four-stage return with multiplier one.
This is the actual signed return used in the note.

I independently differentiated its system. With
\(d_1=L^2ab\), the exact derivatives are
\[
b_y=iab(1+Lz),\quad
(d_1)_z=d_1L(1+La),\quad
(d_1)_y=d_1[2/y+iz+ia(1+Lz)].
\]
They give every entry in the printed real \(3\times3\) Jacobian, including
the plus sign in \(\partial_t(\Im b+t)=\Re d_1+1\).

The retained matrix is an exact decimal-rational approximation. The sum
of all nonnegative interval entry bounds safely dominates its infinity
operator norm. The two strict directed inequalities make
\(v\mapsto v-Af(v)\) a contraction of the closed real box into itself.
The center norm gate also implies \(A\) is invertible. Thus its unique
fixed point solves the original three-variable system. The separate stage
separations and \(S_1\ne0\) gates establish the primitive marked history
and simple-parabolic return.

Reality of the residue also has an exact analytic reason: the local
antiholomorphic diffeomorphism \(H\) fixes the point and commutes with
\(F=H^2\). It antiholomorphically conjugates \(F\) to itself; hence its
conjugacy-invariant iterative residue equals its complex conjugate.
Together with the directed real enclosure, this proves strict negativity.
This explanation was sent to the author for inclusion.

For the equal-count alternating history, the four-stage return is the
second iterate of the two-stage Dottie germ. Direct jet composition gives
\(\rho(f^2)=\rho(f)/2\), agreeing with the retained positive value.
The note explicitly preserves each arrangement, return and parameter.

The replay reproduced the full integer enumerations, formal Euler products,
critical-series check, independent 220-digit Jacobian and jet calculations,
strict box inclusion, four phase separations, action, cyclic residues and
the signed parabolic comparison at 1024 directed bits.
