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

The ring implications take reference positivity, the retained signed margin, and the full omitted signed bound as hypotheses. The [transitive axiom audit](DottieQuarticVerification.lean) runs in `lake build` and accepts `propext`, `Classical.choice`, and `Quot.sound`. The checked source replays and their outputs are in the [verification record](../verification/dottie-quartic/README.md). The adapted Gauss-sum sources use the upstream [Apache-2.0 license](murphy-gauss/LICENSE) and [notice](murphy-gauss/UPSTREAM-NOTICE.md).
