# Same-point Dedekind readings from the mixed theta integral

Take a number field $K$ and write $P$ for AxiomMath's mixed theta pair. Write $Z_K$ for any continuation that agrees with the ideal-counting Dirichlet series on $\Re w>1$. Lean uses the identity theorem to compare continuations at the **same** point $w$.

For $0<\Re w<1$, the two readings are

$$
U_K(w)=w(1-w)\int_1^\infty\bigl(t^{w-1}+t^{-w}\bigr)\bigl(P.f(t)-P.f_0\bigr)\,dt,
\qquad V_K(w)=P.f_0.
$$

Lean proves $U_K(w)-V_K(w)=w(1-w)A_K(w)Z_K(w)$, where $A_K$ is the nonzero completion factor in the open strip. Therefore a Dedekind zero is exactly equality of the two readings. The reflection theorem takes a zero at $w$ to a zero at $1-\overline w$ for every number field in any Lean universe. The explicit formula uses the universe-zero field type of the upstream mixed theta construction.

## Cut the integral at a finite height

Let $U_{K,R}$ use the integral from $1$ to $R\ge 1$. The two powers of $t$ in the integrand each have modulus at most one when $0\le\Re w\le1$. Given a complex axis $a$, the signed error satisfies

$$
\Im\bigl(a[U_K(w)-U_{K,R}(w)]\bigr)
\le 2\,\lvert a w(1-w)\rvert\int_R^\infty \lvert P.f(t)-P.f_0\rvert\,dt.
$$

If the imaginary part of $a[U_{K,R}(w)-V_K(w)]$ plus this allowance is strictly negative, the exact reading differs from $V_K(w)$ and excludes a zero at that point. A Dottie measuring region can supply $w$ and an axis. Coverage of the desired strip and a strict finite-integral margin on the measuring regions are the next proof inputs.

- [Continuation, reflection and exact equality](DedekindMixedTheta.lean)
- [Folded integral, signed tail and pointwise exclusion](DedekindMixedThetaTail.lean)
- [Build and axioms](replay-and-axioms.txt)
- [Mixed theta source](https://github.com/AxiomMath/DedekindZetaZeroFree/tree/09afbb4ce6570c1615d58509dc197fc9f0956b7d/DedekindZetaZeroFree/Theta)

## Replay

Check out these sources with `core.autocrlf=false`. Use PowerShell 7.4 or later and a bin directory for Lean `v4.35.0-rc3` (compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`). Clone [DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree) and check out commit `09afbb4ce6570c1615d58509dc197fc9f0956b7d`. Run `lake exe cache get` in that checkout with its pinned toolchain to download the imports. The replay checks the Mathlib revision as well as the Lean version.

```powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin>
```

The replay stages the sources under the upstream checkout's `.lake` directory. It builds only the mixed theta and Mellin imports needed here, then checks the local sources with warnings treated as errors and prints the transitive axioms.

## Sample the measuring circumference

If I divide the two readings by $w(1-w)$ on the open strip, their difference has the same zero test. The pole term stays exact, and the tail allowance becomes $2\int_R^\infty |P.f(t)-P.f_0|\,dt$ for a unit axis.

If I take $m+1$ rational samples in each quadrant of a circle of radius $r$, every point of the circumference is within $2r/m$ of a sample. If the signed sample values stay negative after adding the variation allowance and the tail, Lean gives the same strict sign on the whole circumference.

[Rational samples](DottieRationalContour.lean) · [Completed reading](DedekindMixedThetaCompletedRings.lean) · [Retained integral variation](DedekindMixedThetaOscillation.lean) · [Whole circumference](DedekindMixedThetaFiniteSamples.lean) · [Build and axioms](mixed-theta-sampled-contours-audit.txt)

Run the replay command with `-SampledContours` to check the sample-to-boundary construction. [Full replay and axiom audit](sampled-contours-release-replay.txt)

## Check the phase on the ring

If three readings have positive successive oriented determinants, one constant rotation cannot put all three below the real axis. The interval check gives this configuration for the completed ordinary zeta function on the radius-$31/128$ circle centered at $3/4+100000001i$.

If a holomorphic weight gives the strict sign around the circle, Lean gives zero exclusion for the original reading at the same input.

[Lean phase proofs](DottieContourPhase.lean) · [Axiom audit](dottie-contour-phase-audit.txt) · [Interval checker](check-completed-phase.py) · [Interval output](completed-phase-diagnostic.txt)

For the actual Cayley circle, Lean checks the comparison at the same input and the implication from signed arcs to zero exclusion on the closed disk. The interval replay checks the arc premise. [Weighted Cayley circle and replay](weighted-cayley-circle.md)

If I start with a candidate zero, Lean places its exact input in a Dottie disk and checks when Alpöge’s growth bound applies there. The same boundary point then reads both corrected native words. [Candidate, disk comparison, and word transfer](alpoge-dottie-bridge.md)

If I repeat the marked lap, the corrected reference picks up $2^w-1$. The interval comparison gives a narrower phase cone on the same circle. For a Dedekind reading, Lean checks an outer-circle majorant and how certified samples and a nonvanishing phase model give a signed margin. [Repeated words and field phase models](word-phase-models.md)

## Build a finite cover from local samples

If every point beyond the band’s near-line clearance has a Dottie disk with passing rational samples, Lean turns those local checks into a finite signed cover. Each disk carries its own axis, positive margin, truncation, sample count, and tail bound. Lean supplies the clearance from the Dedekind continuation and uses compactness to choose finitely many disks. The `-SampledContours` replay includes this implication. [Certificate and assembly](DedekindMixedThetaSampleCover.lean) · [Lean type and axiom output](mixed-theta-sample-cover-audit.txt)

## When finite samples recover the sign

If the completed reading has a strict sign on the circumference in one direction, a finite Mellin cutoff and rational mesh will pass. Normalize the direction to unit length. With full margin $\delta>0$, allocate $\delta/4$ each to truncation error at the sample, variation between samples, the tail allowance, and the certified margin. The finite-cover equivalence keeps the same disks and near-line clearance. [Disk and cover equivalence](DedekindMixedThetaSampleCompleteness.lean) · [Lean types and axioms](mixed-theta-sample-completeness-audit.txt)

## One mass bound for a whole band

Let $C_K$ be the constant term of the field’s mixed theta pair and $M_K=2\int_1^\infty\lVert f_K(t)-C_K\rVert\,dt$. If $M_K<\lVert C_K\rVert/[1+(L+31/128)^2]$, Lean supplies the signed band certificate from $-L$ through $L$. The extra $31/128$ accounts for the largest disk radius. This is an explicit bound to certify for the chosen field. [Band theorem](DedekindMixedThetaPoleDominance.lean#L111) · [Lean types and axioms](mixed-theta-pole-dominance-audit.txt)

## Resolve the theta mass by ideal class

For each ideal class let $m_c$ be the integral of the norm of its angular theta remainder on $(1,\infty)$. The class remainders are nonnegative real values, so $M_K=2\alpha_K\sum_c m_c$. The pole constant has norm $\alpha_K h_K$, where $h_K$ is the class number. The common positive factor cancels. The band passes if $2\sum_c m_c<h_K/[1+(L+31/128)^2]$. [Exact class split and band theorem](DedekindMixedThetaClassMass.lean) · [Lean types and axioms](mixed-theta-class-mass-audit.txt)

Let $R_K=\Re\Lambda_{0,K}(1)$, the finite theta integral with the poles kept separate. At $1$ the two Mellin weights add to $1+1/t$. Lean gives $R_K\le M_K\le 2R_K$. A certified upper bound on $2R_K$ can supply the mass test, and a certified lower bound on $R_K$ can rule it out at the chosen height. [One-value bound](DedekindMixedThetaRegularPartBound.lean) · [Lean types and axioms](mixed-theta-regular-part-bound-audit.txt)

## Rational-field calibration

For $\mathbb Q$, each ideal norm has one ideal. The mixed theta pair gives the ordinary completed zeta regular part and $f_{0,\mathbb Q}=1$. At $w=1$, Lean checks
$$
R_{\mathbb Q}=1+\frac{\gamma-\log(4\pi)}{2}<\frac{13}{500},
$$
where $\gamma$ is the Euler–Mascheroni constant. The exact harmonic sum uses `decide +kernel`. Then $2R_{\mathbb Q}<1/[1+(4+31/128)^2]$, so the Dottie certificate covers $-4\le\Im w\le4$. The same-point Dedekind continuation is nonzero over that full height band for $1/2<\Re w\le31/32$.

[Lean normalization](DedekindRationalCalibration.lean) · [Lean bound and band](DedekindRationalDottieBand.lean) · [Normalization audit](dedekind-rational-calibration-audit.txt) · [Band audit](dedekind-rational-dottie-band-audit.txt)

## Read the band input from a field factor

If $\zeta_K(w)=\zeta(w)B(w)$ on $\Re w>1$, include the completion ratio in the cofactor $F(w)=(A_K(w)/\Gamma_{\mathbb R}(w))B(w)$. If $F$ is holomorphic on $\Re w>0$, Lean gives
$$
f_{0,K}=F(1),\qquad \Lambda_{0,K}(1)=F(1)\Lambda_{0,\mathbb Q}(1)+F'(1).
$$
If this value clears the regularized-one inequality, Lean provides the finite signed cover on $[-L,L]$. [Factor and band theorems](DedekindMixedThetaFactorSlope.lean) · [Axiom audit](mixed-theta-factor-slope-audit.txt)

For $K=\mathbb Q(i)=\mathbb Q(\zeta_4)$, Lean gives discriminant $-4$, signature $(0,1)$, and the holomorphic weighted beta factor $F(w)=4^{w/2}\Gamma_{\mathbb R}(w+1)L(w,\chi_4)$. The Gaussian band theorem takes the identity $\zeta_K=\zeta L(\cdot,\chi_4)$ in the convergence half-plane and the strict slope inequality for the chosen $L$. [Gaussian-field theorem](DedekindGaussianQuadratic.lean) · [Lean type and axioms](dedekind-gaussian-quadratic-audit.txt)

## Actual Gaussian local Euler factors

At $p=2$ the Gaussian field has one prime of residue degree one. If $p\equiv1\bmod4$, there are two primes of degree one. If $p\equiv3\bmod4$, there is one prime of degree two. Lean checks these statements over the ring of integers of $\mathbb Q(\zeta_4)$. [Prime counts and degrees](DedekindGaussianPrimeDegrees.lean) · [Axiom audit](dedekind-gaussian-prime-degrees-audit.txt)

Then for every rational prime $p$ and $z\in\mathbb C$,
$$
\prod_{\mathfrak P\mid(p)}(1-z^{f(\mathfrak P/p)})
=(1-z)(1-\chi_4(p)z).
$$
[Local Euler theorem](DedekindGaussianLocalEuler.lean) · [Axiom audit](dedekind-gaussian-local-euler-audit.txt)

## Assemble the field Euler product

For any number field $K$, each nonzero prime ideal belongs to the finite fiber above a unique rational prime. If $\Re w>1$, Lean groups the actual Dedekind Euler product by these fibers and uses the residue degrees in each denominator. [Prime-ideal equivalence](DedekindRationalPrimeFibers.lean) · [Grouping theorem](DedekindEulerByRationalPrime.lean) · [Axioms](dedekind-euler-rational-prime-audit.txt)

For $\mathbb Q(i)$ the checked local factors then give $\zeta_K(w)=\zeta(w)L(w,\chi_4)$ in the convergence half-plane. The Dottie theorem now takes the weighted beta inequality at $w=1$ for the chosen $L$. The `-SampledContours` replay builds the prime-ideal Euler import and runs these modules in order. [Same-toolchain factorization and band theorem](DedekindGaussianEulerProduct.lean) · [Exact Lean types and axioms](dedekind-gaussian-euler-product-audit.txt)

## Cofinal signed bands for any number field

I use the Cureton–Thorner zero-free bound on $\Re w>31/32$. Lean identifies its continuation with the mixed theta continuation by the identity theorem, so the bound applies to the same function as my contour readings. [Cureton–Thorner preprint](https://hexagonmath.org/2610.00200v2) · [AxiomMath theorem](https://github.com/AxiomMath/DedekindZetaZeroFree/blob/09afbb4ce6570c1615d58509dc197fc9f0956b7d/DedekindZetaZeroFree/Main.lean#L9) · [Lean transport](DedekindCuretonThorner.lean)

If my certified intervals cover every nonnegative height, Lean gives Dedekind RH for the field. In particular, for every natural height $N$ it suffices to give a finite signed Dottie boundary certificate on some $[0,M]$ with $M\ge N$. A negative-height zero conjugates to a positive-height zero. A zero on the left reflects to the right at the same height. Any resulting candidate with $1/2<\Re w\le31/32$ falls into a certified band. Lean accepts either the pole-cleared reading or the completed reading used in the finite quadrature and field factorization criteria. [Cofinal theorems](DedekindMixedThetaRightEdge.lean) · [Exact Lean types and axioms](right-edge-replay-and-axioms.txt)

On a bounded band, Lean already gives a positive clearance next to the critical line and a finite cover of the remaining rectangle. The band certificate needs a cover with a strictly negative rotated reading around each measuring circle. [Clearance and finite cover](../../../lean-ideal73/DedekindFiniteDottieCover.lean) · [Boundary certificate](../../../lean-ideal73/DedekindCofinalSignedRings.lean)

Run the replay with the same pinned checkout and toolchain used above. The right-edge replay also builds AxiomMath’s zero-free theorem.

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -RightEdge
~~~
