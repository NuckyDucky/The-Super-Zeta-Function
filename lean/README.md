# Lean verification

The starting point is the ordered map

$$F_L(P,M)=(\exp(LM),\exp(-LP)),\qquad g_L(z)=\exp(L\exp(-Lz)).$$

Following the first coordinate through two steps gives $g_L$. Following its derivative at a fixed pair gives the product of the lifted logarithms. Setting that product equal to one leads to the characteristic equation. The formalization also goes in reverse, reconstructing the ordered fixed pair from a characteristic phase.

## Reproduce the build

Install [elan](https://lean-lang.org/install/) and Python 3. From the repository root run

```sh
python tools/check_lean.py --fetch-cache
```

The toolchain file pins Lean 4.19.0. The Lake manifest pins mathlib and its dependencies. The first run downloads the precompiled imports. For subsequent local runs, use `python tools/check_lean.py`. Alternatively, from this directory, run `lake build` and `lake env lean Audit.lean`. The proof build uses the Lean kernel. The audit visits every theorem in the imported project modules and checks its axiom dependencies against `propext`, `Classical.choice`, and `Quot.sound`. It rejects proof placeholders and project axioms. The same check runs on GitHub.

## Follow the mathematics

| Result | Exact scope and Lean entry point |
| --- | --- |
| [Reciprocal lift](SuperZeta/Reciprocal.lean) | `translated_two_base` gives the affine translation. `step_twice`, `cap_even`, and `cap_odd` retain the order of the phases. `parabolic_characteristic` derives $a^2\exp(a-a^{-1})=-1$ from balance and multiplier one. |
| [Dottie fold](SuperZeta/Dottie.lean) | `existsUnique_dottie` isolates $d=\cos d$ in $(0,\pi/2)$. `centerline_fixed` constructs the actual pair. `stationary_iff_dottie` and `dottie_curvature_neg` identify the unique stationary point on this interval and prove a quadratic fold. |
| [Finite spire periods](SuperZeta/Reciprocal.lean) | `centerline_scalar_period` gives $p/\gcd(p,2)$ for the squared half-step. `cap_capture` proves capture and primitive period from a closed contracting return, entry of the marked cap, and divisor exclusions. The three numerical witnesses are [replayable separately](../archive/2026-11-18-lean-foundations-v001/checks/dottie_slice.py). |
| [Quartet and cosine determinant](SuperZeta/Quartet.lean) | `determinant_root_iff` identifies the full zero set of $\cos^2u-u^2$ with the image of the characteristic phases; `recover_fixed_pair` recovers the two exponentials, their lifts and the unit multiplier. |
| [Differential system](SuperZeta/Flow.lean) | `response` differentiates the two original local fixed equations in logarithmic time to obtain the derivatives of $a=(U+V)/2$ and $\mu=UV$ wherever $1-\mu\ne0$. `transverse_flow` proves the evolution of $\mu-a^2$ in regular time. |
| [Ordered germs](SuperZeta/Germ.lean) and [selected radius](SuperZeta/Order.lean) | `actual_order_contrast` differentiates both real nested exponential functions four times. Their fourth Taylor coefficients differ by $k(k-1)(k-2)/12$. `contrast_strict_max` and `selected_radius` yield $r=2-\sqrt3$ for the limiting real contrast. The Hurwitz connection here is the explicit Bernoulli polynomial. |
| [Marked spire disks](SuperZeta/SpireDisk.lean) | `propagate` proves the nonlinear image-radius bound including center rounding. `chain_sound` controls derivatives through every ordered stage. `paired_period_of_even` proves that two scalar clocks of period $320$ yield ordered period $640$. |
| [Touchard derivatives and coefficient fields](SuperZeta/Touchard.lean) | `return_derivatives` proves the all-orders Touchard recurrence. For $\alpha\ne0,-1$, `joint_coefficient_field` proves $\mathbb Q(h_3,h_4)=\mathbb Q(\alpha)$ for the actual normalized Taylor coefficients. |
| [Meme quadratic](SuperZeta/Meme.lean) | `coefficient_quartic`, `equal_target_iff` and `signed_gap` check the inverse branches, the quartic and $2.37\times10^{-20}< R(e)-T(\pi)<2.91\times10^{-20}$. [MemePrecision](SuperZeta/MemePrecision.lean) sharpens the signed gap to $(2.6231439430444,2.6231439430445)\times10^{-20}$. The same proof bounds $\pi-\widehat\pi$ between $8.682007272724\times10^{-20}$ and $8.682007272726\times10^{-20}$. |
| [Spectral traces and Riemann coordinates](SuperZeta/Spectrum.lean) | `determinant_hasSum` gives the actual cosine series at all complex arguments. `newton_convolution` and `first_four_unit_coupling_traces` derive $2,10/3,92/15,3538/315$ from its logarithmic derivative. `quartet_mode_norm` gives the exact magnitude of one complex mode. `equality_iff_riemann_zero` proves the consequence of the stated reconstruction identity using mathlib’s Riemann zeta. |
| [Binary valuation](SuperZeta/Binary.lean) | `determinant_valuation` gives the determinant coefficient valuation at every degree from two onward. [BinaryLaw](SuperZeta/BinaryLaw.lean) proves `trace_digit_law` directly for every trace of the coupled determinant. [BinaryReference](SuperZeta/BinaryReference.lean) proves the reference and difference each have one fewer factor of two. [BinaryInteger](SuperZeta/BinaryInteger.lean) gives the odd integral normalization. |
| [Riemann reference and correction](SuperZeta/Reference.lean) | `reference_double_root` gives the exact leading coefficient at a reference root. `reference_hasSum` identifies the doubled half-integer spectrum with the scaled Riemann zeta for $\Re s>1/2$. `correction_differentiable` proves holomorphy for $\Re s<1$ at nonnegative inverse squared coupling. `residue_half` computes the residue of the reference plus this correction at $s=1/2$. |
| [Stieltjes integral for each root](SuperZeta/Stieltjes.lean) | `slit_integral` evaluates the resolvent integral on the principal cut for $0<\Re s<1$. `countable_slit` proves the interchange with an infinite spectral sum given absolute summability and a uniform angular margin. |
| [Entire correction](SuperZeta/MellinContinuation.lean) and [special values](SuperZeta/SpecialValues.lean) | `entireCorrection_differentiable` extends the actual relative Mellin integral to all complex $s$. `entireCorrection_succ` gives its positive integer values from the actual log kernel’s even Taylor coefficients. `regularized_determinant` computes $4$ from the derivative at zero of the reference plus correction. |
| [Factorial quarter correction](SuperZeta/Barnes.lean) | With $D_n=\pi n[4^{-n}\binom{2n}{n}]^2$, `quarter_bounds` gives finite bounds and `quarter_limit` proves $n(1-D_n)\to1/4$ from Wallis’ product. `quartet_barnes_product` gives the finite identity under the displayed Gamma recurrence. [QuartetRadius](SuperZeta/QuartetRadius.lean) proves existence at every positive level, $R_n-2\pi n\to0$ and the quarter limit for $R_nB_n^2/2$. |
| [Meme quartic descent](SuperZeta/Hasse.lean) | `quartic_forces_negative_square` maps every hypothetical rational projective point to a nonzero negative-square abscissa on the explicit elliptic curve. [HasseCover](SuperZeta/HasseCover.lean) proves that one of four fixed rational inputs yields a point over every $\mathbb Q_p$. [HasseLocal](SuperZeta/HasseLocal.lean) also checks all nine archived bad primes. The rank and squareclass computation used in `obstructed_by_four_classes` is recorded in the [arithmetic archive](../archive/2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md). |
| [Finite-window recovery](SuperZeta/Recovery.lean) | `cell_lower_bound` uses the maximum-modulus principle on a zero-free quotient. The result turns a certified boundary estimate into a bound throughout a cell around a simple zero. `on_line_of_cofinal_counts` proves the global implication given equality of cumulative counts along cofinal checkpoints. The [archived contours](../archive/2026-11-18-superzeta-distance-v001/) certify specified finite windows. |

## Where the formal boundary lies

The complex cosine roots, the analytic determinant, and its formal Taylor coefficients now have machine proofs. Passing from those coefficients to the infinite spectral root sums still requires the canonical product. Lean now evaluates the reference Dirichlet series and constructs the relative Mellin integral. Identifying their sum with the coupled spectral root series still needs a proof in Lean. `equality_iff_riemann_zero` takes this final reconstruction as a hypothesis. The same distinction applies to the [large-height mode estimate](../archive/2026-11-18-lean-foundations-v001/checks/complex_values.py), whose summed tail bound is currently a written proof.

The [source collection](../archive/2026-11-18-lean-foundations-v001/README.md) records which remaining results have manuscript proofs, arithmetic computations or directed numerical certificates.
