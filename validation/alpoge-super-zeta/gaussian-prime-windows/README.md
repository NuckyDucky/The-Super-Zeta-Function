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
- If I take the common divisor of the coefficients across all starting values and apply Möbius inversion to its prime exponents, the extra terms give only $O(\sqrt x\log x)$ in the cumulative count. The centered sum of those ideal norms has the same window criterion. [Written common-divisor argument](gaussian-relative-determinant.md#the-common-divisor-over-all-starting-values)
- If an upper comparison uses only Frobenius in a fixed Galois CM field, it gives both central branches the same reading. The paired majorant has mean at least $3/4$ for the Gaussian count, against the target mean $1/2$. The written density argument uses the group totals checked in Lean. [Finite group calculation](GaussianCMPrimeBarrier.lean) · [Density argument](gaussian-relative-determinant.md#what-the-fixed-cm-place-data-can-distinguish)

## Replay

Use Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Build the quartic package and run the [parent bridge replay](../README.md#replay) to prepare its library and the pinned Alpöge modules. Then, from this directory, run the following with the same Lean binary and compiled libraries.

```powershell
.\replay-gaussian-prime-windows.ps1 -LeanExecutable $leanBinary -SuperZetaLibrary $superZetaLibrary -MathlibPackages $mathlibPackages
```

The script builds seventeen modules in dependency order with one Lean worker. Its output directory defaults to a fresh temporary directory. The axiom audits together list only `propext`, `Classical.choice`, and `Quot.sound`. [Replay script](replay-gaussian-prime-windows.ps1) · [First twelve modules](replay-audit.txt) · [Conductor and weight transfer replay](conductor-residue-replay-audit.txt) · [Relative determinant and CM comparison replay](relative-determinant-replay-audit.txt)

For the real-axis positivity proof, use Lean 4.19.0 and first prepare the compiled [quartic kernel checkpoint](../../../verification/quartic-kernel/README.md#run-the-replay). Pass its directory and the Lean 4.19.0 Mathlib packages to this replay. The two drivers use their matching Lean and Mathlib pins.

```powershell
.\replay-quartic-real-positivity.ps1 -LeanExecutable $lean419 -QuarticKernelLibrary $quarticCheckpoint -MathlibPackages $mathlib419Packages
```

[Positivity replay script](replay-quartic-real-positivity.ps1) · [Positivity replay output](quartic-real-positivity-audit.txt)

