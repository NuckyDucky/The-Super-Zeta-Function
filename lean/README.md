# Lean proofs for The Super Zeta Function

For a real analytic function on a closed height interval with nonzero endpoint values, the product of the endpoint signs gives the parity of its interior zeros counted with their analytic orders. Lean constructs the finite set of zeros and proves the same rule after subtracting a real target. The accompanying Gaussian calculation encloses both endpoint values at the Dottie height. [Endpoint parity](SuperZeta/GaussianEndpointParity.lean) · [Numerical signs and unresolved case](../archive/2026-11-20-gaussian-endpoint-parity-v001/README.md)

The paper develops the quadratic and its two real ovals, the ordered iteration and its Dottie fold, and the cosine determinant. [Main paper](../README.md#the-quadratic-and-the-genus-one-curve)

For an isolated pair of solutions, Lean recovers their signed squared separation from two power sums, classifies its sign under reflection in the critical line, and proves the collision criterion when these sums vary continuously. The companion complex-analysis proof identifies the weighted circle integrals giving the sums. The rectangular enclosure for the particular Gaussian Hecke factor uses a separate interval calculation. [Two-root algebra and continuity](SuperZeta/TwoRootMoments.lean) · [Weighted circle integrals](SuperZeta/TwoRootCircleIntegral.lean) · [Gaussian enclosure and assumptions](../archive/2026-11-20-gaussian-two-root-transition-v001/README.md)

For the period-640 extension, `full_twisted_spectrum` factors the determinant over its complete zero set, `rootProbes_recover_mark` recovers the unit return direction, and `return_from_fresh_root_sums` proves the inverse on a monotone branch. The directed orbit calculation supplies the finite branch and period bounds. [Formal inverse](SuperZeta/Oriented/SpectralInverse.lean) · [Period-640 evidence](../archive/2026-11-19-oriented-return-v001/README.md#returning-to-the-witness)

The ordered iteration and its two-step return on the first coordinate are

$$
F_L(P,Q)=(e^{LQ},e^{-LP}),\qquad g_L(z)=e^{L e^{-Lz}}.
$$

At a fixed pair put $U=LQ$ and $V=-LP$. The multiplier of the return is $UV$. When $UV=1$, the fixed-pair equations give the characteristic equation $U^2e^{U-U^{-1}}=-1$. The converse constructs the fixed pair from a solution of this equation. [Reciprocal iteration](SuperZeta/Reciprocal.lean) · [Converse](SuperZeta/Quartet.lean)

## Ordered lifts and arithmetic factors

At a fixed pair I keep the two actual exponents $U=LQ$ and $V=-LP$.
For $\tau=U/V\ne 1$ and $V\ne0$, their difference $d=V-U$ records the logarithm of $-\tau$.
Lean checks the inverse formulas $V=d/(1-\tau)$, $U=\tau V$ and $L=U/e^V$ against the original ordered map. At $\tau=i$ a marked vector $mV+nU$ reads $m+ni$ after division by $V$. [Inverse lift and marked vectors](SuperZeta/DedekindLift.lean)

For the character modulo three, Lean checks all prime-power weights and the analytic zero multiplicities of the products $\zeta L$ and $\zeta^7 L$ away from $w=1$. The identification of the first product with the Eisenstein field zeta function uses the classical field factorization. For the six-coefficient quartic, Lean checks the Gaussian factorization, the discriminant criterion for a root, and direct enumeration at $p=13,37,73$. At $73$ the two conjugate reductions give zero and two roots respectively. [Prime weights, product orders and Gaussian branch tests](SuperZeta/FieldWeights.lean)

For a marked vector $z=m+ni$, the three explicit Legendre symbols can distinguish $z$ from its conjugate. Lean checks the three residue substitutions into the quartic discriminant and proves that multiplying the two readings gives the product of the three symbols evaluated on $m^2+n^2$. The identification with the branch field's Hecke character uses Gaussian quadratic reciprocity in the written argument. [Conjugation and norm](SuperZeta/FieldWeights.lean)

## Run the proofs

Install [elan](https://lean-lang.org/install/) and Python 3. From the repository root run

~~~sh
python tools/check_lean.py --fetch-cache
~~~

The repository fixes Lean at version 4.19.0 and records the exact mathlib revision in the Lake manifest. The first run downloads precompiled dependencies. Subsequent runs can omit `--fetch-cache`. From this directory, the equivalent commands after fetching the dependencies are `lake build` and `lake env lean Audit.lean`.

Lean checks each proof. The audit checks that each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, and rejects proof placeholders and new axioms. GitHub runs the same build and audit. To see the statement and hypotheses of a theorem, use `#check` in a Lean file in this directory.

~~~lean
import SuperZeta

#check SuperZeta.Reciprocal.step_twice
#check SuperZeta.QuartetRadius.exists_characteristic_quarter
#check SuperZeta.Hasse.every_prime_affine_point
~~~

## Reciprocal iteration

| Result | Lean statement |
| --- | --- |
| [Translation and ordered return](SuperZeta/Reciprocal.lean) | `translated_two_base` gives the affine translation. `step_twice`, `cap_even` and `cap_odd` identify the return and its two possible starting phases. `parabolic_characteristic` gives the characteristic equation. |
| [Dottie fold](SuperZeta/Dottie.lean) | `existsUnique_dottie` proves the unique solution of $d=\cos d$ in $(0,\pi/2)$. `centerline_fixed` constructs the fixed pair. `stationary_iff_dottie` and `dottie_curvature_neg` prove the quadratic fold. |
| [Periodic orbits](SuperZeta/Reciprocal.lean) and [disk estimates](SuperZeta/SpireDisk.lean) | `centerline_scalar_period` relates the period $p$ of an orbit to the period $p/\gcd(p,2)$ for the squared map. `cap_capture` proves capture and primitive period from a contraction and the exclusion of shorter returns. `propagate` bounds the image of a disk, including the rounding of its center. `chain_sound` bounds the derivative of the composition. `paired_period_of_even` gives the ordered period $640$ from two scalar periods of $320$. [Numerical verification of the three parameters](../archive/2026-11-18-lean-foundations-v001/checks/dottie_slice.py) |
| [Differential equations](SuperZeta/Flow.lean) | `response` differentiates $a=(U+V)/2$ and $\mu=UV$ in the coordinate $L=L_0e^t$ where $1-\mu\ne0$. `transverse_flow` gives the equation for $\mu-a^2$ after the change of time variable. |
| [Taylor coefficients](SuperZeta/Germ.lean) and [their fourth-order difference](SuperZeta/Order.lean) | `actual_order_contrast` proves that reversing the two normalized exponentials changes the fourth Taylor coefficient by $k(k-1)(k-2)/12$. `contrast_strict_max` and `selected_radius` give $r=2-\sqrt3$ at the maximum of the limiting real difference. The relation to Hurwitz zeta is expressed by a Bernoulli polynomial. |
| [Touchard polynomials](SuperZeta/Touchard.lean) | `return_derivatives` gives the recurrence for all derivatives of the return. `joint_coefficient_field` proves $\mathbb Q(h_3,h_4)=\mathbb Q(\alpha)$ for the normalized Taylor coefficients when $\alpha\ne0,-1$. |

## Cosine determinant and spectral zeta

| Result | Lean statement |
| --- | --- |
| [Characteristic phases and roots](SuperZeta/Quartet.lean) | `determinant_root_iff` identifies the roots of $\cos^2u-u^2$ with the images of the characteristic phases. `recover_fixed_pair` reconstructs the ordered fixed pair and proves its multiplier is one. |
| [The complete root list](SuperZeta/QuartetLevels.lean) | `existsUnique_level` proves that every positive index determines a unique quartet. `determinant_root_iff_indexed_square` and `family_injective` identify each squared root with exactly one index. [The entire determinant in the squared variable](SuperZeta/CoupledDeterminant.lean) has simple zeros and satisfies $\lVert E(w)\rVert\le\exp(2\sqrt{\lvert w\rvert})+\lvert w\rvert$. |
| [Determinant coefficients and their logarithmic derivative](SuperZeta/Spectrum.lean) | `determinant_hasSum` gives the power series for the determinant. `newton_convolution` and `first_four_unit_coupling_traces` give the first four coefficients of its negative logarithmic derivative, $2,10/3,92/15,3538/315$. `quartet_mode_norm` gives the modulus of an individual complex term. |
| [The factor of two in each coefficient](SuperZeta/BinaryLaw.lean) | `trace_digit_law` proves that the two-adic valuation in degree $n$ is the number of ones in the binary expansion of $n+1$. The [reference coefficients and their differences](SuperZeta/BinaryReference.lean) each have valuation one less. The [integer normalization](SuperZeta/BinaryInteger.lean) gives odd integers. |
| [Reference zeta and Mellin correction](SuperZeta/Reference.lean) | `reference_double_root` gives the leading coefficient at a double root of the reference determinant. `reference_hasSum` evaluates its spectral series in terms of $\zeta(2s)$ on $\Re s>1/2$. `correction_differentiable` proves holomorphy of the correction on $\Re s<1$ for nonnegative inverse squared coupling. `residue_half` gives the residue of the reference plus correction at $s=1/2$. |
| [Euler’s sine product and the reference resolvent](SuperZeta/ReferenceProduct.lean) | Euler’s sine product gives $\cosh x=\prod_{n\ge0}(1+x^2/\lambda_n)$. The [logarithmic derivative](SuperZeta/ReferenceResolvent.lean) sums the resolvents with the doubled multiplicities of the reference spectrum. |
| [Stieltjes integral](SuperZeta/Stieltjes.lean) | `slit_integral` evaluates the resolvent integral using the principal branch on the slit plane for $0<\Re s<1$. `countable_slit` allows interchange with a countable spectral sum under absolute summability and a uniform bound away from the cut. |
| [Entire continuation of the correction](SuperZeta/MellinContinuation.lean) | `entireCorrection_differentiable` extends the Mellin correction to every complex $s$. `entireCorrection_succ` evaluates it at positive integers using the Taylor coefficients of the integrand. [Special values](SuperZeta/SpecialValues.lean) include the regularized determinant $4$. |
| [Zeros under the change of variable](SuperZeta/Multiplicity.lean) | `reconstruction_order` proves that $F(s)=2\pi^{-2s}(2^{2s}-1)\zeta(2s)$ preserves the order of the zero at $w=2s$ throughout $0<\Re s<1/2$. The point $1/2+iT$ corresponds to $1/4+iT/2$. |
| [Distance from a simple zero](SuperZeta/Recovery.lean) | `cell_lower_bound` uses the maximum-modulus principle on the reciprocal of $F(s)/(s-s_i)$ to turn a boundary estimate into an inequality throughout a rectangle containing one simple zero. `on_line_of_cofinal_counts` gives the all-height implication if total counts and critical-line counts agree along heights tending to infinity. [Numerical certificates for the specified rectangles](../archive/2026-11-18-superzeta-distance-v001/README.md) |

At unit coupling, `UnitSpectrum.determinant_product` proves the product identity for every complex argument. The finite-disk proof removes all enclosed simple roots. The determinant’s growth bound forces the normalized quotient to tend to one as the disks expand. On $1/2<\Re s<1$, `UnitSpectrum.root_hasSum` identifies the convergent series of squared roots with its analytic continuation. On $0<\Re s<1/2$, the continuation equals the entire correction exactly where $\zeta(2s)=0$. [Finite-disk factorization](SuperZeta/DeterminantProduct.lean) · [Canonical roots and reconstruction](SuperZeta/UnitSpectrum.lean)

The local strengthening of the seven-eighths theorem uses interval arithmetic for the argument-principle counts and Hardy $Z$-function signs. The numerical certificates supply the hypotheses of Lean’s distance theorem in the stated rectangles. The [comparison on the main page](../README.md#a-local-strengthening-of-the-seven-eighths-theorem) gives the exact intervals and counts. The [large-height estimate](../archive/2026-11-18-lean-foundations-v001/checks/complex_values.py) uses a separate written proof of the sum over the omitted terms.

For the two angles $+\pi/6$ and $-\pi/6$, the local transfer specializes the externally proved Dirichlet bound at Liu’s endpoint to Riemann zeta and carries both sides of the strip through $w=2s$. Lean separately checks the equality of multiplicities, reflection of a differentiable Hurwitz zero path and nonvanishing of the arithmetic quotient in its velocity. The kernel also checks that Liu’s moment equation (33), after the change of variable (35), is equivalent on the comparison interval to the tracker’s exact endpoint polynomial. The angular derivative formula and the speed estimates have a written proof, with the numerical endpoints enclosed by ball arithmetic. [Lean statements and hypotheses](SuperZeta/Oriented/LiuEndpointTransfer.lean) · [Angular velocity and its verification](../archive/2026-11-20-liu-angular-velocity-v002/README.md)

## Factorial and arithmetic results

For two lists of exponential sign phrases, `rooted_phrase_order_iff` gives a criterion for equality of their cap values at every fixed real lift $L>0$. Concatenating the phrases in each list must give the same individual signs in the same order. Lean checks that `++--`, `--++`, and `-+-+` have distinct cap values even though all three use two positive and two negative stages. For a fixed complex lift $L\ne0$, `phrase_map_order_iff` gives the same criterion for equality of the entire functions. At the particular lift $L=\pi i$, every nonempty word started at $1$ reaches $-1$ and stays there. [Chronological order, phrase boundaries and the exceptional cap](SuperZeta/SignWords.lean)

At $L=\pi i$, let $W$ be the composition of the stages in their specified order, acting on a variable cap $z$. For the six four-stage words with two signs of each kind, Lean proves that $W(1)=-1$ and $W'(1)=\pi^4$ for all six, and that their six values of $W''(1)$ are pairwise distinct. For a word of any finite length, $W'(1)$ is nonzero and the single complex number $W''(1)/W'(1)$ uniquely determines the word, including its length. [Derivatives of the exponential stages](SuperZeta/CapRecovery/CapJets.lean) · [Proof of injectivity](SuperZeta/CapRecovery/Dominance.lean)

The same ratio can be computed using the earlier detector's coefficients at powers of 2. Begin at exponent zero and add two for each positive stage and one for each negative stage. At exponent $m$ the normalized prime coefficient is $1+(-1)^m/7$, so subtracting one and multiplying by seven gives the product of the signs read so far. Lean checks the sum of these prefix readings against the derivatives of $W$. It also proves the formula for a known nonzero real weight in place of $1/7$, and shows how one uncentered endpoint coefficient together with the first derivative and the word length recovers an unknown weight. [Character at 2 and its prefix readings](SuperZeta/CapRecovery/DyadicWeights.lean) · [Exact derivative formula](SuperZeta/CapRecovery/DyadicCap.lean) · [Weight calibration](SuperZeta/CapRecovery/GeneralWeights.lean)

At 73, `MarkedBranch.shellWords73` recovers the two quartic sign orders from the root counts in the two residue fields. `capValues73` evaluates those words at base 2 and cap 1, giving $\sqrt{2}$ and $1/4$. For any finite list of unramified pairs with a specified order and a nonzero fourth angular harmonic, `shell_cap_roundtrip` proves that the ordinary and angular coefficients recover a word whose exponential endpoint decodes to the same letters. The decoder accepts any upper bound on the number of stages. [Angular coefficients and quartic root counts](SuperZeta/MarkedBranch.lean) · [Signed logarithm decoder](SuperZeta/SignWords.lean)

For the completed-zero reading, `ZeroMoment.hasSum_zero_moment` differentiates locally uniformly convergent normalized products on an open neighborhood of the evaluation point. The limit must be nonzero at that point, which must also differ from each indexed root. The theorem then gives the sum over roots with multiplicity. `signedMoment_conj` proves that conjugating every root reverses the sign of the measurement. The [arithmetic application](../archive/2026-11-20-gaussian-branch-spectrum-v001/README.md) supplies the Hecke product representation from the cited theory and encloses the value via the Euler series. [Lean hypotheses and proofs](SuperZeta/ZeroMoment.lean)

For the normalized Hurwitz speed, Lean checks the finite sum over a reflection-permuted list of the actual Dirichlet quotients, the nonnegative squared difference, and the evaluation of the diagonal after separation by powers of three. The height asymptotic and the short-window estimate use the analytic proofs cited in §3.12. [Formal statements](SuperZeta/Oriented/HurwitzSpeedMoment.lean) · [Mean-square proof and data](../archive/2026-11-20-hurwitz-speed-mean-square-v001/README.md)

For the two-input spectrum I use the principal powers of `UnitSpectrum.squaredRoot`. Lean checks conjugation on exchanging the inputs, the squared-norm diagonal, recovery of the original convergent root sum on its Mellin strip, and the trigonometric identities that isolate each quartet’s angular contribution. The infinite-plane uniqueness theorem has a written proof. FLINT checks the inversion from five real totals. [Lean statements](SuperZeta/Oriented/TwoInputSpectrum.lean) · [Proof and numerical verification](../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-input-spectrum.md)

| Result | Lean statement |
| --- | --- |
| [Factorial correction](SuperZeta/Barnes.lean) | For $D_n=\pi n[4^{-n}\binom{2n}{n}]^2$, `quarter_bounds` bounds the error at finite $n$ and `quarter_limit` proves $n(1-D_n)\to1/4$ using Wallis’ product. `quartet_barnes_product` gives the finite product using the Gamma recurrence. [QuartetRadius](SuperZeta/QuartetRadius.lean) proves $R_n-2\pi n\to0$ and the quarter limit for $R_nB_n^2/2$. |
| [Exact Stirling remainder](SuperZeta/StirlingCorrection.lean) | `log_D_factorial` identifies the cancellation of the factorial errors, and `log_C_eq_radial_sub_laplace` gives the exact integral. `factorialRemainder_hasSum` recovers the logarithmic error for one factorial by summing the same integral at successive doublings. `factorial_eq_stirling_mul_exp_dyadic` gives the resulting equality for $n!$ at every positive integer. [The truncation proof](SuperZeta/StirlingExpansion.lean) bounds the combined remainder by the first omitted term at every order and proves the corresponding bound for the sum above a cutoff. |
| [The deformed zeta near zero](SuperZeta/DeformedZeta.lean) | `continuation_eq_series` restores the subtracted terms in the region of convergence. `residue_zero` gives residue $-\nu/4$ and `spectralZeta_analyticAt_zero` proves regularity of the spectral diagonal, with value $-1/4$. |
| [Factorial phase](SuperZeta/FactorialPhase.lean) | `phaseFactor_quotient` gives the exact phase of the neighboring power factors. `dottie_factorial_bracket` proves the half-turn comparison from the exact decimal coordinates of the two reflected Dottie parameters. `dottie_quartet_bracket` proves the full comparison given the [directed radial bounds](../archive/2026-11-18-stirling-correction-v001/phase-bounds.json). |
| [The quadratic for π](SuperZeta/Meme.lean) | `coefficient_quartic` and `equal_target_iff` check the quartic and inverse branches. `rootGap_min` proves the exact minimum root separation of one at $N(x)=0$, and `roots_at_zero_numerator` identifies the two roots. [MemePrecision](SuperZeta/MemePrecision.lean) bounds $R(e)-T(\pi)$ between $2.6231439430444\times10^{-20}$ and $2.6231439430445\times10^{-20}$, and $\pi-\widehat\pi$ between $8.682007272724\times10^{-20}$ and $8.682007272726\times10^{-20}$. |
| [Local points and rational descent](SuperZeta/Hasse.lean) | `quartic_forces_negative_square` sends a hypothetical rational projective point to a nonzero negative-square abscissa on the associated elliptic curve. [HasseCover](SuperZeta/HasseCover.lean) proves that one of four rational inputs gives a point over $\mathbb Q_p$ at each prime $p$. [HasseLocal](SuperZeta/HasseLocal.lean) checks the nine exceptional primes individually. The exclusion of rational points uses the rank and squareclass computation in the [written descent](../archive/2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md). |

The [source collection](../archive/2026-11-18-lean-foundations-v001/README.md) locates the manuscripts, arithmetic computations and numerical certificates.
