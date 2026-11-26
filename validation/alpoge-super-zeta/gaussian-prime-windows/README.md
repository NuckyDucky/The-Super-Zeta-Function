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

## Replay

Use Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Build the quartic package and run the [parent bridge replay](../README.md#replay) to prepare its library and the pinned Alpöge modules. Then, from this directory, run the following with the same Lean binary and compiled libraries.

```powershell
.\replay-gaussian-prime-windows.ps1 -LeanExecutable $leanBinary -SuperZetaLibrary $superZetaLibrary -MathlibPackages $mathlibPackages
```

The script builds the twelve modules in dependency order, uses one Lean worker, and prints their theorem types and transitive axiom audits. Its output directory defaults to a fresh temporary directory. The checked build records only `propext`, `Classical.choice`, and `Quot.sound`. [Replay script](replay-gaussian-prime-windows.ps1) · [Replay output](replay-audit.txt)

For the real-axis positivity proof, use Lean 4.19.0 and first prepare the compiled [quartic kernel checkpoint](../../../verification/quartic-kernel/README.md#run-the-replay). Pass its directory and the Lean 4.19.0 Mathlib packages to this replay. The two drivers use their matching Lean and Mathlib pins.

```powershell
.\replay-quartic-real-positivity.ps1 -LeanExecutable $lean419 -QuarticKernelLibrary $quarticCheckpoint -MathlibPackages $mathlib419Packages
```

[Positivity replay script](replay-quartic-real-positivity.ps1) · [Positivity replay output](quartic-real-positivity-audit.txt)

