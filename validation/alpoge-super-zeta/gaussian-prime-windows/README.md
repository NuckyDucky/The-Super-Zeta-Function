# Gaussian prime windows for the Dedekind quartic

For the archived quartic $K$, the exact factorization is $\zeta_K(w)=\zeta(w)\beta(w)G(w)$. If the rational Dirichlet result is supplied, an off-line Dedekind zero in the critical strip forces a zero of the actual Gaussian factor $G$ at the same input $w$. This packet makes the one remaining prime-window input explicit. [Checked field reduction](../../../lean-ideal73/ArchivedQuarticZeroTransport.lean) · [Rational Dirichlet proof and verification](https://math.mit.edu/~drew/shortgrh/)

- If $\Re w>1$, the archived Euler weights give the exact series for $-G'(w)/G(w)$. [Coefficient theorem](ArchivedGaussianLogDerivative.lean)
- If I check the original upper bound at the endpoints and at the prime powers inside a given window, then it holds throughout that window. [Finite window check](GaussianPrimeWindowKnots.lean)
- If I absorb the higher powers into the linear correction, the original window condition and the prime-only condition imply one another. The exponent and window width are the same. The constant can change. [Exact correction and equivalence](GaussianPrimeOnlyWindow.lean)
- If I take an odd power of a rational prime, its weight is the first prime weight. If I take an even power, its weight comes from rational quadratic characters or from the specified Euler factor at a prime dividing $2D$. For every positive integer modulus there is a conjugate pair of common norm coprime to that modulus with opposite Gaussian signs. [Prime supports and parity](GaussianPrimeSupport.lean) · [Conjugate norm check](GaussianNormOrientation.lean)

## Exact Lean conclusion

```lean
AlpogeSuperZeta.quartic_rh_of_archived_gaussian_prime_only_windows
  (hD : DirichletLZerosOnLine)
  (hcut : ArchivedGaussianPrimeOnlyWindowBound) :
  DedekindZetaRH QuarticModel.K
```

For every $1/2<\theta<1$, `hcut` asks for a positive $\delta$, a nonnegative constant $C$, and arbitrarily late starts $Y$ such that the corrected prime-only ramp is at most $Cx^\theta$ throughout $[Y,Y^{1+\delta}]$. Dividing by $x$ gives the one-sided normalized bound $Cx^{\theta-1}$. [Definition and theorem](GaussianPrimeOnlyWindow.lean) · [Actual build and axiom output](replay-audit.txt)

The written Frobenius calculation uses the supplied Dirichlet theorem to control the combined count. It then identifies the upper bound on the smoothed completely split prime count of the normal closure that would supply `hcut`. A separate calculation identifies the leading $-2\sqrt{x}$ contribution of the higher powers to the original ramp under the same Dirichlet input. These derivations use classical Chebotarev estimates. [Completely split primes](gaussian-prime-classes.md) · [Odd and even series and square cutoff](gaussian-prime-squares.md)

## The lower bound and inert Gaussian primes

- If I fold the original theta kernel on the real axis, the checked positive prefix sums give a strictly positive completed Gaussian reading at every real input. If I reverse the signed ramp, the pole detector still works because the Gaussian poles in its half-plane have nonzero imaginary part. [Real-axis proof](QuarticPositiveReal.lean) · [Lower-window proof](GaussianLowerPrimeWindow.lean)
- If $U(p)$ counts the unramified Gaussian primes of degree one above $p$ and $I(p)$ counts the inert ones among them, Lean gives $a(p)=U(p)-2I(p)$. The rational Dirichlet input controls the base count. An upper bound on the centered inert count on cofinal windows therefore supplies the lower-bound input for the quartic. [Exact prime weights](GaussianInertPrimeWeights.lean) · [Centering and the remaining estimate](gaussian-inert-windows.md)

```lean
AlpogeSuperZeta.quartic_rh_of_lower_windows_and_real_positivity
  (hD : DirichletLZerosOnLine)
  (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
  (hcut : ArchivedGaussianPrimeOnlyLowerWindowBound) :
  DedekindZetaRH QuarticModel.K
```

The 4.19.0 replay proves `hpos` for the shared formula. The 4.33.1 replay identifies that formula with the field's Mellin transform and gives the implication with `hpos` as an explicit argument. [Shared formula](QuarticRealFormula.lean) · [4.19.0 positivity audit](quartic-real-positivity-audit.txt) · [4.33.1 window audit](replay-audit.txt)

## Conductor residues and the unramified character

- If an odd rational prime $p$ splits in $\mathbb Q(i)$, then the sign at a marked prime $\mathfrak p$ above $p$ is $-1$ exactly when $\delta^{(p-1)/2}+1\in\mathfrak p$, where $\delta=-5045155+1027708i$. At $73$, Lean checks this at both conjugate primes and finds exactly one factor of $73$ in the norm. [Conductor and divisibility proofs](GaussianConductorResidue.lean)
- The written field calculation gives $G(w)=L_B(w,\psi)$ for an unramified order-four ideal class character of $B=\mathbb Q(\sqrt{-D})$. It also gives $G(w)^2=L_A(w,\eta_A)$ for an unramified quadratic character of $A=\mathbb Q(i,\sqrt D)$. Lean checks the conductor arithmetic and the change in prime weights. With the rational Dirichlet input, the centered inert count over $A$ has the same window criterion as the original count. [Field calculation](gaussian-biquadratic-class-character.md) · [Lean weight transfer](GaussianBiquadraticInertWeights.lean)

## Relative Frobenius and the determinant

- If $b_n$ is the coefficient of $u$ in $(1+i+u)^n$ with $u^2=\delta$, then its reductions at $n=p+1$ and $n=p-1$ read the negative and positive signs at the same marked prime. The determinant $-\delta b_n^2$ carries the square of that prime ideal. At the two primes over $73$ the norm-one rotation has exact orders $74$ and $72$. [Lean residue and determinant](GaussianRelativeDeterminant.lean) · [Lean rotation and orders](GaussianRelativeFrobenius.lean)
- If I divide the determinants at $p+1$ and $p-1$, the terms linear in $p$ cancel in the log norm. At index $73$ this ratio has norm valuation $-8$ at $5$. The sum of the contributions from primes other than the matching prime is part of the estimate. [Size and valuation calculation](gaussian-relative-determinant.md)
- If I take the ideal generated by the coefficients across all starts, then its containment in $\mathfrak q^k$ is equivalent to the negative archived sign and $(N\mathfrak q+1)\ell^{k-1}\mid n$, where $\ell$ is the rational prime under $\mathfrak q$. Lean applies Möbius inversion to these exact containment counts and weights each surviving occurrence by $\log N\mathfrak q$. [Lean prime powers](GaussianCommonDivisorPowers.lean) · [Lean Möbius transform](GaussianCommonDivisorMoebius.lean) · [All-index cutoff and Dirichlet series](gaussian-relative-determinant.md#the-dirichlet-series-of-the-primitive-ideal-norms)
- If I subtract the Gaussian base prime count and adjust the linear term, then the upper window bound on the common-divisor indices is equivalent to the lower bound on the original signed prime ramp. Both use $[Y,Y^{1+\delta}]$ and the same exponent $\theta>1/2$. This gives the quartic field implication with the existing rational Dirichlet and real-axis positivity inputs. [Exact weights](GaussianIndexMoebiusWeights.lean) · [Window theorem](GaussianPrimitiveIndexWindow.lean) · [Lean replay and axiom audit](index-window-replay-audit.txt)
- If the Gaussian factor vanishes at $\rho$ to the right of the critical line, then the Mellin transform of the centered common-divisor ramp has a simple pole at $\rho$. The squared cutoff moves the pole to $s=\rho/2$ and keeps the same residue. Lean proves that the all-index correction is analytic on $\Re w>1/2$. [Mellin continuation and half-address theorem](GaussianPrimitiveIndexMellin.lean)
- If I read the determinant common divisors at their original integer indices, I can test the sum over $[x/2,x)$ directly. Counting all positive multiples introduces the ordinary zeta factor. The product $(w-1)\zeta(w)$ extends through $w=1$. With the rational Dirichlet input, this product and the half-window multiplier $1-2^{-w}$ are both nonzero on $\Re w>1/2$, so each Gaussian pole there survives. [Finite raw window](GaussianRawWindowCounts.lean) · [Exact Mellin transform](GaussianDivisorWindow.lean) · [Quartic criterion](GaussianRawWindowCriterion.lean)
- If I replace the counts of multiples at addresses up to $\sqrt{x}$ by their lengths, the total change is bounded by $D_\theta x^\theta$ for every $\theta>1/2$. The same quartic implication then uses the resulting window with only the larger-address counts exact. [Square-root split](GaussianRawWindowRounding.lean)
- If I count multiples in $[x/2,x)$, I get the number of odd multiples below $x$. This lets me move the degree-one addresses from $p+1$ to $p$ and absorb the higher-degree and prime-power addresses into the linear correction, with total error at most $D_\theta x^\theta$ for $1/2<\theta<1$. The quartic implication now takes a bound on the finite prime sum, with the same windows and exponent. [Odd multiples and sparse terms](GaussianHalfWindowMultiplicity.lean) · [Centered shift](GaussianCenteredHalfWindowShift.lean) · [Prime-only window and quartic theorem](GaussianRawPrimeWindow.lean)
- If I use the real quadratic base $\mathbb Q(\sqrt D)$, its two residue roots give the same signed prime coefficient. Lean keeps the original coefficients at the excluded primes and checks equality of the whole prime-only window at every cutoff. [Real quadratic weights](GaussianRealQuadraticWeights.lean) · [Build and axiom output](real-quadratic-replay-audit.txt)
- If I hold the two mixed evaluation points fixed for the identity and central Frobenius labels, a two-by-two minor gives different norm valuations at $5$ and $13$ and two zeros at $73$. Lean checks the extra divisors at $7$ and $61$ and verifies that the larger fixed matrix has a unit minor at both primes for each label. If the rows on the identity graph contain $X^p$ and $Y^p$, every full-row ordinary-derivative minor vanishes modulo $p$. Lean checks the same obstruction for any nonzero $F^p$ in the row span with $F$ vanishing on the sampled points. [Fixed minor](GaussianFrobeniusFixedMinor.lean) · [Larger matrix and general obstruction](gaussian-relative-determinant.md#a-larger-matrix-at-the-same-primes) · [Build and axiom output](frobenius-jet-replay-audit.txt)
- If I repeat the same marked divisor addresses below $x$ and weight each by $(1-n/x)^2$, the Mellin transform has the extra factor $2/((w+1)(w+2))$. Lean carries the same one-sided window criterion to that squared cutoff and to the full prefix. Lean also checks the per-prime error from Kominers's floor-weighted triangle to the squared weight. [Quartic declarations](GaussianDivisorSquaredWindow.lean) · [Triangle error](GaussianFrobeniusTriangle.lean) · [Build and axiom output](gaussian-squared-cutoff-replay-audit.txt)
- If an upper comparison uses only Frobenius in a fixed Galois CM field, it gives both central branches the same reading. The paired majorant has mean at least $3/4$ for the Gaussian count, against the target mean $1/2$. The written density argument uses the group totals checked in Lean. [Finite group calculation](GaussianCMPrimeBarrier.lean) · [Density argument](gaussian-relative-determinant.md#what-the-fixed-cm-place-data-can-distinguish)

- If two spectral formulas read the same target at the same $w$ with nonzero factors, they give the same zero test. A measured gap excludes a zero when it exceeds the certified error. The original unit Super Zeta and the painted Gaussian $j,k$ comparison supply both exact readings in Lean, for any additional list of order comparisons. [Thermometer declarations](SpectralThermometer.lean) · [Build and axiom output](spectral-thermometer-audit.txt)

## Replay

Use Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Build the quartic package and run the [parent bridge replay](../README.md#replay) to prepare its library and the pinned Alpöge modules. Then, from this directory, run the following with the same Lean binary and compiled libraries.

```powershell
.\replay-gaussian-prime-windows.ps1 -LeanExecutable $leanBinary -SuperZetaLibrary $superZetaLibrary -MathlibPackages $mathlibPackages
```

The script builds forty-six modules in dependency order with one Lean worker. Its output directory defaults to a fresh temporary directory. The raw-window audit builds six modules from source using the earlier twenty-seven-module replay. The prime-only audit builds four further modules from source against those thirty-three. The real-quadratic and fixed-minor audits build the next two modules in order from source. The Frobenius jet audit builds three modules against that checkpoint. The squared cutoff audit builds fifteen modules from source against the earlier twenty-seven, including the changed modules, their dependents, and the three new modules. The axiom audits together list only `propext`, `Classical.choice`, and `Quot.sound`. [Replay script](replay-gaussian-prime-windows.ps1) · [First twelve modules](replay-audit.txt) · [Conductor and weight transfer replay](conductor-residue-replay-audit.txt) · [Relative determinant and CM comparison replay](relative-determinant-replay-audit.txt) · [Common divisor and Möbius replay](common-divisor-replay-audit.txt) · [Common divisor window replay](index-window-replay-audit.txt) · [Raw determinant window replay](raw-window-replay-audit.txt) · [Prime-only half-window replay](prime-half-window-replay-audit.txt) · [Real-quadratic coefficient replay](real-quadratic-replay-audit.txt) · [Fixed Frobenius minor replay](fixed-frobenius-minor-replay-audit.txt) · [Frobenius jet replay](frobenius-jet-replay-audit.txt) · [Squared cutoff and triangle replay](gaussian-squared-cutoff-replay-audit.txt) · [Thermometer replay](spectral-thermometer-audit.txt)

For the real-axis positivity proof, use Lean 4.19.0 and first prepare the compiled [quartic kernel checkpoint](../../../verification/quartic-kernel/README.md#run-the-replay). Pass its directory and the Lean 4.19.0 Mathlib packages to this replay. The two drivers use their matching Lean and Mathlib pins.

```powershell
.\replay-quartic-real-positivity.ps1 -LeanExecutable $lean419 -QuarticKernelLibrary $quarticCheckpoint -MathlibPackages $mathlib419Packages
```

[Positivity replay script](replay-quartic-real-positivity.ps1) · [Positivity replay output](quartic-real-positivity-audit.txt)

