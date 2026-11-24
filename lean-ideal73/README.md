# The quartic field at 73

This package constructs the field $E=\mathbb Q(i,\sqrt{-5045155+1027708i})$ and recovers it from the root of the original quartic. The norm in the theorem is mathlib’s absolute ideal norm in the ring of integers of this field. There are exactly two integral ideals of norm 73. They both have residue $i=46$ in $\mathbb F_{73}$, with the square root of the discriminant reducing to 9 or 64. The other prime above 73 has residue degree two and norm 5329.

| Source | Step proved |
|---|---|
| [Original quartic branch](OriginalQuarticBranch.lean) | The root of the Gaussian quadratic generates the same rational field. |
| [Integral field model](QuarticModel.lean) | The monic quartic for the integral generator is irreducible and is its minimal polynomial. |
| [Good reduction](GoodPrime.lean) | The order exponent is prime to 73, so reduction of the minimal polynomial detects the maximal order. |
| [Prime-norm coefficient](PrimeIdealCoefficient.lean) | Ideals of prime norm correspond to residue maps. At a good prime their number equals the number of roots of the reduced polynomial. |
| [The actual count](QuarticAt73.lean) | Mathlib’s subtype of ideals of this field with norm 73 has cardinality two. |
| [All primes above 73](PrimeDecomposition73.lean) | The three specified primes exhaust the list. All are unramified, and their residue degrees are 1, 1 and 2. |
| [Ideals of every power of 73](PrimePowerIdealCount.lean) | Unique factorization identifies the ideals of norm $73^n$ with triples $a+b+2c=n$. The even and odd formulas count these actual ideals. |
| [Transfer to the field statement](FieldCoefficientTransfer.lean) | For this field, agreement of multiplicative coefficients at every prime power identifies the three-factor product under explicit holomorphy and series hypotheses. The critical-line conclusions for the Riemann and beta factors then reduce the field question to the Gaussian factor. |
| [Two Gaussian zeros of each field continuation](GaussianZeroFiber.lean) | Under the same ideal-series hypotheses, every field continuation has value zero at the two supplied Gaussian zeros. A spectral reading that distinguishes those points cannot be recovered from the field value alone. |
| [One midpoint hit in the right ring](QuarticRingMidpoint.lean) | Given the product identification and the two class identities, either class sum reaching half its total at one input refutes the field's RH statement. With the Riemann and beta factors nonzero at that input, a zero of any admissible continuation is equivalent to such a hit. |
| [Slope on a rectangle](DerivativeRectangle.lean) | Reflection and a strict upper bound on the imaginary derivative locate all zeros in that rectangle on the line. Opposite-sign endpoint values give a unique simple zero. |
| [Exhaustion by rectangles](StripCover.lean) | For a continuous Gaussian factor with reflecting zeros, positive lower bounds on each compact rectangle in the right-half-strip exhaustion imply the critical-line assertion at all heights. |

Run the following commands from this directory with elan installed. The toolchain file selects Lean 4.33.1. The lockfile pins mathlib and its dependencies. The first command obtains the compiled mathlib imports. The second builds the field modules and checks the principal theorems’ transitive axiom dependencies against the three foundational axioms allowed by the project.

~~~sh
lake exe cache get $(sed -n 's/^import \(Mathlib\.[[:alnum:]_.]*\)$/\1/p' *.lean | sort -u)
lake build
~~~

The [spectral library](../lean/README.md) uses its own pinned Lean 4.19 toolchain. For the comparison of its corrected trace with the field’s ideal-counting series, see [the proof and independent PARI calculation](../docs/proofs/gaussian-ideals-and-super-zeta.md). With PARI/GP on the path and python-flint installed, run the comparison from the repository root.

~~~sh
python -B tools/check_quartic_ideal_series.py
~~~

## The exact Dottie quartic and the signed ring test

The Lean 4.33.1 audit builds the archived Gaussian factor from the same quartic field, proves its root number is $+1$, and identifies the three-factor product with the field's Dedekind zeta. The two smoothed norm sums reproduce its normalized completion throughout $0<\Re w<1$. The remainder after removing the retained ranges is exactly the signed sum over the omitted norms.

| Source | Step checked by Lean |
|---|---|
| [Conductor and field](QuarticConductorSign.lean) | The exact Gauss amplitude, theta reflection, and Dedekind-zeta identification. |
| [Smoothed contour and the two Hamilton orders](ArchivedDottieSmoothedIdentity.lean) | The full sum and its partition, and the sign and order conclusions on the two Dottie rings given the signed numerical bounds. |
| [Gamma phase](DottieReferencePhaseEnclosure.lean) | The direction at $\tfrac12+i(T_D-\tfrac1{512})$ has a phase between $4.067324$ and $4.067326$ radians modulo $2\pi$. |
| [Exact reference projection](DottieReferenceMoment.lean) | The archived reference unit is a positive multiple of the absolute real projection of the rotated signed polynomial through norm $276{,}824{,}064$. |
| [Signed Taylor moments](DottieSignedMoments.lean) | The 17 factorial-divided moments recover the unscaled reference polynomial with error below $3\times10^{-30}$. The proof bounds the absolute mass by counting the original signed rows. |
| [Original Super Zeta address and the quartic](ArchivedQuarticSpectralAddress.lean) | The right and reflected addresses are distinct. The field zero test and signed ring implications use the ordered Hamilton readings at the actual spectral addresses. |

| [Signed lattice mass](DottieMomentMass.lean) | The absolute weighted coefficient mass through norm $N$ is at most $2\lfloor\sqrt N\rfloor$ by grouping lattice rows by their maximum coordinate. |
| [Completed phase and rational reference](DottieRationalProjection.lean) | A single real projection of the original signed sum at exact rational inputs implies positivity of the archived reference unit if it exceeds $1/10$. The transfer costs less than $3/50$ in the unscaled projection. |
| [Integer logarithm enclosures](DottieNormLog.lean) | Integer arithmetic yields proved lower and upper ticks for $\log n$, with a uniform error bound for $1\le n\le 2^{29}$. |

| [Integer reference score](DottieReferenceScore.lean) | The fixed-denominator score differs from the exact rational projection by at most $1/25$. Lean proves positivity of the original reference unit if the integer score exceeds $7/50$ of its denominator. The original signed weights are implemented by [the executable Jacobi recurrence](DottieRowSign.lean). |

| [Reference score blocks](DottieScoreChunks.lean) | Disjoint blocks cover each row, including its final short block. The [first 1,024-point block](DottieFirstReferenceBlock.lean) has an exact kernel-checked score. [Integer phase reduction](DottieCosRescale.lean) preserves both cosine endpoints and leaves previously generated candidate values valid. |

| [Cached integer log](DottieQuickScore.lean) | Six leading bits index a kernel-verified table. Eight residual Horner terms preserve the 120-tick log enclosure and the original score error budget. |
| [Paired Gaussian score](DottieSymmetricChunks.lean) | Swapping positive coordinates preserves the norm. The sum evaluates each off-diagonal pair once and skips the cosine when its two signs cancel. Lean checks the block partition and its connection to reference positivity. |
| [Exact signed norm ranges](ArchivedDottieRangeIntegral.lean) | The omitted part is four finite intervals. Its contribution is the sum of two contour integrals with the exact signed Gaussian Dirichlet polynomials. |
| [Circle budgets](ArchivedDottieRetainedBudget.lean) | The retained and [omitted](ArchivedDottieOmittedBudget.lean) implications expose the sharper finite-prefix margin and the lower, middle, and far error budgets. |
| [Sharp moments](DottieSharpCircleMoments.lean) | Seventeen factorial-divided moments approximate the retained sharp polynomial uniformly on the right circle and its reflection. [The Gamma ratio](DottieGammaRatio.lean) gives a separate complex relative enclosure. |
| [One-sided horizontal slope](DottieOmittedHorizontalSlope.lean) | Reflection expresses the joint sharp and middle contribution as the difference of two values at the same height. A derivative upper bound of $94 S_0$ gives the exact $188x S_0$ premise for the ring. |
| [Packed sign witnesses](DottieWitnessPairBlocks.lean) | Modular squares check the largest-prime sign in each orientation. Each 32-bit code is unpacked in Lean and the result proves the original paired block total. |
| [Reference scale](DottieReferenceQuantitative.lean) | The original integer threshold yields a lower bound of 2 × 10⁻³⁰ for the reference. Once the row equality is supplied, it also gives the original relative far budget. |
| [All three short bands](DottieBandArchivedShort2.lean) | All 12,288 original short-band coefficients pass kernel replay. The short bands near K/4, K/2 and K have terminal sums −136, −80 and 18. |
| [Relative sharp-circle bound](DottieSharpRelativeCircle.lean) | The exact Gamma ratio and reflected Taylor model reduce the signed margin to a bound in relative units and transport an angular cover to the measuring circle. |
| [Retained band batch replay](DottieBandArchivedShort4096.lean) | Kernel-checked Lucas tables, exact prime-power coefficients and signed chunk joins certify the first complete short band. Its terminal sum is −136 and all prefix sums lie in [−140, 30]. |
| [First checked band chunk](DottieBandPrimePowers.lean) | Lean checks the first fifteen zero coefficients and the following coefficient of two using a Lucas certificate and the two exact Gaussian addresses. The resulting 16-slot chunk has the integer sum format of the retained-band estimate. |
| [Integrated retained-band estimate](DottieRetainedBandBounds.lean) | The exact Gamma integral and its reflection meet the finite-band allowance given three signed integer sum bounds. The original Hamilton ring test now takes those arithmetic inputs and the archived signed margins. |
| [Signed finite-band variation](DottieBandVariation.lean) | Abel summation bounds the exact contour polynomial from signed integer partial sums and a terminal mass. The phase-length allowance of one third is checked for each of the three original merged intervals. |
| [Retained band and tail split](DottieRetainedBands.lean) | The six finite bands form three contiguous intervals. The infinite retained tail is bounded by 2 × 10⁻³⁹. A sharp margin of 190.37 permits a finite-band bound of 3.6 × 10⁻³⁴ at the proved reference threshold. |
| [Finite lower smoothing](DottieLowerFullBudget.lean) | A finite rectangle avoids the Gamma poles. The left segment, horizontal edges and original right-line exterior give an absolute 1.8 × 10⁻³⁸ bound for each paired discrepancy. The same argument supplies both original smoothing budgets from the row equality. |
| [Absolute far budget](DottieFarNumeric.lean) | The exact omitted far terms have norm at most 4 × 10⁻³⁴ on the Dottie rectangle. The reference Gamma ratio is bounded below in [DottieReferenceGammaLower](DottieReferenceGammaLower.lean). |
| [Far contour shift](DottieRightContourShift.lean) | Moves the exact finite far block and its reflected side to the line of real part seven. The [coefficient count](DottieMomentMass.lean) also gives the absolute norm prefix bound N + floor(sqrt N). |
| [Smoothed contour derivative](DottieRangeDifferentiation.lean) | The exact derivative is taken under the middle range contour by a Gaussian majorant. The [joint horizontal derivative](DottieJointOmittedDerivative.lean) combines it with the sharp side and reduces the signed circle budget to the bound of $94 S_0$ on that derivative. |
| [Completed sharp derivative](DottieSharpBlockDerivative.lean) | Differentiates the exact lower sharp contribution and bounds the error from moving away from its signed anchor. |
| [Faster paired sign](DottieStructuralPairBlocks.lean) | Two kernel-checked residue masks and a structurally recursive Jacobi remainder preserve every archived Gaussian sign and the same exact score. Row 11,000 replays using the lookup path. |
| [Exact omitted sharp block](DottieOmittedSharpVariation.lean) | The actual lower omitted contribution is a completed Dirichlet block on the right circle and its reflection. A uniform error follows from a bound on the ordered signed partial sums. |
| [Even norm reuse](DottieDyadicNormBlocks.lean) | The exact quartic satisfies $a_{2n}=a_n$. The even part of the first omitted sharp interval is the measured preceding half-range times $2^{-w}$. |
| [Reference score candidate](DottieReferenceCandidate.lean) | Lean checks the strict integer margin for the complete candidate sum. Positivity follows once the full Lean row span equals that integer. [Row 11,000](DottiePairedRow11000.lean) replays a large row of the actual certificate. |
| [Signed block variation](DottieSignedBlockVariation.lean) | Summation by parts gives uniform complex-weight and log-weighted bounds conditional on a signed partial-sum bound for the block. |
| [Signed patch cover](ArchivedQuarticSignedPatchCover.lean) | A strictly positive rotated real part on each member of a finite box cover implies the existing box-margin criterion. |
| [First 32 paired rows](DottieFirstPairedRows.lean) | The score for the first 32 paired rows is kernel-checked. Whole spans add to the exact 16,638-row sum by the [span assembly theorem](DottiePairedRows.lean). |
| [First complete reference row](DottieFirstReferenceRow.lean) | All 16,639 points with real coordinate 1 were checked in 17 kernel blocks and assembled into one exact integer. |


To replay the complete first row, run `lake build DottieFirstReferenceRow`.

The ring implications take reference positivity, the retained signed margin, and the full omitted signed bound as hypotheses. The [transitive axiom audit](DottieQuarticVerification.lean) runs in `lake build` and accepts `propext`, `Classical.choice`, and `Quot.sound`. The checked source replays and their outputs are in the [verification record](../verification/dottie-quartic/README.md). The adapted Gauss-sum sources use the upstream [Apache-2.0 license](murphy-gauss/LICENSE) and [notice](murphy-gauss/UPSTREAM-NOTICE.md).
