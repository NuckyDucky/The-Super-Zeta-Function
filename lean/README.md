# Lean proofs for The Super Zeta Function

The research overview introduces the quadratic and its two real ovals, the ordered iteration and its Dottie fold, and the cosine determinant. [Research overview](../README.md#the-quadratic-and-the-genus-one-curve)

The ordered iteration and its two-step return on the first coordinate are

$$
F_L(P,Q)=(e^{LQ},e^{-LP}),\qquad g_L(z)=e^{L e^{-Lz}}.
$$

At a fixed pair put $U=LQ$ and $V=-LP$. The multiplier of the return is $UV$. When $UV=1$, the fixed-pair equations give the characteristic equation $U^2e^{U-U^{-1}}=-1$. The converse constructs the fixed pair from a solution of this equation. [Reciprocal iteration](SuperZeta/Reciprocal.lean) · [Converse](SuperZeta/Quartet.lean)

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

The formal proof of the spectral reconstruction in $1/2<\Re s<1$ uses genus-zero Hadamard factorization as a hypothesis in `reconstruction_of_genus_zero`. Lean supplies the growth bound, the normalization, the complete simple zero list, and convergence of the product. It then differentiates the product and evaluates the Mellin integral. [Reconstruction theorem](SuperZeta/CoupledProduct.lean) · [Proof guide](../archive/2026-11-18-quartet-levels-v001/README.md)

The local strengthening of the seven-eighths theorem uses interval arithmetic for the argument-principle counts and Hardy $Z$-function signs. The numerical certificates supply the hypotheses of Lean’s distance theorem in the stated rectangles. The [comparison on the main page](../README.md#a-local-strengthening-of-the-seven-eighths-theorem) gives the exact intervals and counts. The [large-height estimate](../archive/2026-11-18-lean-foundations-v001/checks/complex_values.py) uses a separate written proof of the sum over the omitted terms.

## Factorial and arithmetic results

| Result | Lean statement |
| --- | --- |
| [Factorial correction](SuperZeta/Barnes.lean) | For $D_n=\pi n[4^{-n}\binom{2n}{n}]^2$, `quarter_bounds` bounds the error at finite $n$ and `quarter_limit` proves $n(1-D_n)\to1/4$ using Wallis’ product. `quartet_barnes_product` gives the finite product using the Gamma recurrence. [QuartetRadius](SuperZeta/QuartetRadius.lean) proves $R_n-2\pi n\to0$ and the quarter limit for $R_nB_n^2/2$. |
| [Exact Stirling remainder](SuperZeta/StirlingCorrection.lean) | `log_D_factorial` identifies the cancellation of the factorial errors, and `log_C_eq_radial_sub_laplace` gives the exact integral. [The truncation proof](SuperZeta/StirlingExpansion.lean) bounds the remainder by the first omitted term at every order and proves the corresponding bound for the sum above a cutoff. |
| [The deformed zeta near zero](SuperZeta/DeformedZeta.lean) | `continuation_eq_series` restores the subtracted terms in the region of convergence. `residue_zero` gives residue $-\nu/4$ and `spectralZeta_analyticAt_zero` proves regularity of the spectral diagonal, with value $-1/4$. |
| [Factorial phase](SuperZeta/FactorialPhase.lean) | `phaseFactor_quotient` gives the exact phase of the neighboring power factors. `dottie_factorial_bracket` proves the half-turn comparison from the witness decimals. `dottie_quartet_bracket` proves the full comparison given the [directed radial bounds](../archive/2026-11-18-stirling-correction-v001/phase-bounds.json). |
| [The quadratic for π](SuperZeta/Meme.lean) | `coefficient_quartic` and `equal_target_iff` check the quartic and inverse branches. `rootGap_min` proves the exact minimum root separation of one at $N(x)=0$, and `roots_at_zero_numerator` identifies the two roots. [MemePrecision](SuperZeta/MemePrecision.lean) bounds $R(e)-T(\pi)$ between $2.6231439430444\times10^{-20}$ and $2.6231439430445\times10^{-20}$, and $\pi-\widehat\pi$ between $8.682007272724\times10^{-20}$ and $8.682007272726\times10^{-20}$. |
| [Local points and rational descent](SuperZeta/Hasse.lean) | `quartic_forces_negative_square` sends a hypothetical rational projective point to a nonzero negative-square abscissa on the associated elliptic curve. [HasseCover](SuperZeta/HasseCover.lean) proves that one of four rational inputs gives a point over $\mathbb Q_p$ at each prime $p$. [HasseLocal](SuperZeta/HasseLocal.lean) checks the nine exceptional primes individually. The exclusion of rational points uses the rank and squareclass computation in the [written descent](../archive/2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md). |

The [source collection](../archive/2026-11-18-lean-foundations-v001/README.md) locates the manuscripts, arithmetic computations and numerical certificates.
