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

## Cyclotomic zeros at the same input

For the Gaussian field, the checked Euler product gives the exact continuation $\zeta_{\mathbb Q(i)}(w)=\zeta(w)L(w,\chi_4)$ at every $w\ne1$. Its strip-zero statement is equivalent to the two corresponding statements for zeta and beta. The `-SampledContours` replay includes this Gaussian continuation. [Gaussian theorem](DedekindGaussianContinuation.lean)

For a positive modulus $m$, put $K=\mathbb Q(\zeta_m)$. At a rational prime $p\nmid m$, the residue degrees and the order of $p$ in $(\mathbb Z/m\mathbb Z)^\times$ give the same Euler denominator as the product over the characters modulo $m$. At $p\mid m$, all those characters vanish at $p$. I collect the actual denominators above these finitely many primes into $B_m(w)$. [Local denominator identity](DedekindCyclotomicLocalEuler.lean)

If $Z$ is any Dedekind continuation for $K$, Lean proves
$$
B_m(w)Z(w)=\prod_{\chi\bmod m}L(w,\chi)
\qquad(w\ne1).
$$
The factor $B_m(w)$ is nonzero when $\Re w>0$. Every prime contribution has $|p^{-w}|<1$ there, and its residue degree is positive. Thus a zero in the open strip occurs at the same input as a zero of at least one Dirichlet factor. The two strip-zero statements are equivalent. [Continuation and zero theorem](DedekindCyclotomicContinuation.lean)

If a field is supplied with a rational embedding into $K$, the entire abelian zeta quotient takes a zero of the embedded field to a zero of $K$ at that same $w$. Lean therefore proves Dedekind RH for the field from the strip-zero statements for the characters modulo $m$. The embedding and the Dirichlet statement are the explicit inputs. [Embedding theorem](DedekindCyclotomicSubfields.lean) · [Exact Lean types and axioms](cyclotomic-replay-and-axioms.txt)

Use the original pinned AxiomMath checkout and Lean toolchain for this replay.

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -Cyclotomic
~~~

## All abelian number fields

If $K/\mathbb Q$ is abelian, Lean now supplies a positive modulus and a rational embedding of $K$ into its cyclotomic field from the pinned Kronecker–Weber proof. If the Dirichlet strip-zero statement holds for every character of every positive modulus, Lean gives Dedekind RH for every abelian number field. Conversely, taking the cyclotomic fields recovers the Dirichlet statement. The input matches `DirichletLZerosOnLine` in the compact replay of Alpöge's proof. [Lean equivalence](DedekindAbelianFields.lean) · [Kronecker–Weber source](https://github.com/AxiomMath/DedekindZetaZeroFree/blob/09afbb4ce6570c1615d58509dc197fc9f0956b7d/vendor/class-field-theory/Lean4/ClassFieldTheory/KroneckerWeber/Core.lean#L68) · [Dirichlet statement](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean#L10)

## Solvable Galois extensions at the same input

If $L/K$ is Galois with solvable group, Lean composes the entire factors along the abelian steps. For the Dedekind continuations of $K$ and $L$ it gives an entire function $g$ with $Z_L(w)=g(w)Z_K(w)$ for every $w\ne1$. A zero of the lower field is a zero of the upper field at the same $w$. If the lower field satisfies Dedekind RH, the upper field satisfies it exactly when the strip zeros of $g$ lie on the line. [Entire factor and zero transfer](DedekindSolvableQuotient.lean)

For a solvable Galois extension $L/\mathbb Q$, Lean chooses the subfield fixed by the commutator subgroup. The rational Dirichlet input handles that abelian subfield. The remaining statement for $L$ is the critical-line result for the entire relative factor. [Field criterion](DedekindSolvableQuotient.lean) · [Exact types and axiom output](field-extensions-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -FieldExtensions
~~~

## Compare the two completed readings on one Dottie circle

If $L/K$ has a solvable Galois group, write $Z_L=gZ_K$. For the two completed readings $A_L$ and $A_K$, Lean gives $A_L=H A_K$ with $H=(\Gamma_L/\Gamma_K)g$. Multiplying by $\overline{A_K}$ gives $A_L\overline{A_K}=H|A_K|^2$. If the signed cross product has margin $\delta>0$ and $|A_K|\le M$ around the circle, then the signed reading of $H$ has margin at least $\delta/M^2$. [Completion and sign transfer](DedekindRelativeDottie.lean)

For truncated samples $A,B$ of the upper and lower readings, let $e_A,e_B$ be the respective tail and variation allowances. Lean uses the cross-product error $e_A(|B|+e_B)+|A|e_B$ and an upper bound for $|B|+e_B$. If the resulting signed circles cover cofinal height bands, Lean assembles the finite covers, obtains the near-line clearance, and uses the right-edge theorem and reflection to finish the strip. [Exact sample inequalities](DedekindRelativeDottieSamples.lean)

For a field with solvable normal closure, Lean transfers a zero to the closure at the same input. The closure's commutator-fixed field takes the Dirichlet strip-zero result. The other input is the cofinal sample condition comparing that fixed field and the closure. [Normal-closure transfer](DedekindSolvableClosure.lean) · [Exact final premises and Lean output](relative-dottie-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -RelativeDottie -BuildThreads 1
~~~

## Cyclic fixed fields and unramified Euler factors

If $L/K$ is Galois and $P$ over $p$ is unramified, then the smallest positive Frobenius power at $P$ that fixes the intermediate field $E$ is $f(Q/p)$, where $Q$ is the prime below $P$ in $E$. The conjugate count at step $n$ is the size of the fixing subgroup times the sum of $f(Q/p)$ over the primes with $f(Q/p)\mid n$. [Frobenius return](DedekindUnramifiedFrobenius.lean) · [Prime count](DedekindPrimeFiberCounting.lean)

Let $H$ run over the cyclic subgroups of $G=\mathrm{Gal}(L/K)$. Lean gives one family of integer weights $a_H$ for every unramified $p$. If $u(d)$ is the invertible factor assigned to residue degree $d$, then

$$
\prod_H\left(\prod_{Q\mid p\text{ in }L^H}u(f(Q/p))\right)^{a_H}
=u(1)^{|G|}.
$$

On $\operatorname{Re} w>0$, take $u(d)=(1-(Np)^{-dw})^{-1}$ for $d>0$. This matches the base Euler factor with the factors of the cyclic fixed fields. [Cyclic weights](DedekindCyclicSubgroupWeights.lean) · [Prime-power coefficients](DedekindCyclicEulerCoefficients.lean) · [Exact product](DedekindCyclicEulerFactors.lean) · [Lean replay and axioms](cyclic-euler-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay-cyclic-euler.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin>
~~~

## Same-input zero transfer for any Galois group

Let $S$ consist of the base primes with a ramified prime above them in $L/K$. For each intermediate field $E$, multiply $Z_E(w)$ by the Euler denominators over $S$. The resulting product uses the primes outside $S$ for $\operatorname{Re} w>1$. The cyclic weights give a finite identity between these corrected zeta values. Lean carries the identity to every $w\ne1$. [Ramified prime set](DedekindFiniteRamification.lean) · [Local factors](DedekindCyclicZetaLocal.lean) · [Continued product](DedekindCyclicZetaProducts.lean)

If $\operatorname{Re} w>0$ and $Z_K(w)=0$ at $w\ne1$, the identity forces a zero of a cyclic fixed field at the same $w$. The finite corrections are nonzero there. The upper extension over that fixed field is cyclic, so its abelian quotient transfers the zero to $Z_L(w)$. If all rational Galois fields satisfy Dedekind RH, then the normal-closure transfer gives Dedekind RH for every number field. [Exact zero transfer and field reduction](DedekindCyclicZetaDescent.lean)

The Dottie version takes two inputs. `hD` places the rational Dirichlet zeros on the line. `hs` supplies completed Mellin sample coverage for each nonabelian Galois field over $\mathbb Q$. At each nonnegative height, Lean needs a band and measuring disks covering the points between its near-line clearance and real part $31/32$. The finite sample bounds must give a strict boundary sign after variation and tail allowances. [Exact sample premise](DedekindGaloisDottieTarget.lean) · [Lean replay and axioms](galois-descent-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay-cyclic-euler.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -GlobalDescent
~~~

## First Dottie disk for the discriminant-23 class product

Take the splitting field of $X^3-X-1$. Lean gives the Galois group $S_3$, identifies the quadratic subfield $\mathbb Q(\sqrt{-23})$, and proves that the relative extension is cyclic of degree three. [Field and group](DedekindDiscriminant23Field.lean) · [Relative extension](DedekindDiscriminant23Quadratic.lean)

If $|w-3/4|\le31/128$, the completed class product has real part at most $-1/400$. Lean identifies the actual completed Dedekind reading at the same $w$ as eight times that product. So its real part is at most $-1/50$ and the field zeta has no zero throughout the closed disk. [Formula and exact bounds](discriminant23-dottie.md) · [Actual field theorem](DedekindDiscriminant23DottieReading.lean) · [Lean output](discriminant23-dottie-field-replay-and-axioms.txt)

If $0<\operatorname{Re}w<1$ and $|\operatorname{Im}w|\le1/2$, multiply the actual completed reading by $w(1-w)$. Lean gives a real-part ceiling of $-3/64$ across the whole band. So the Dedekind zeta of the splitting field is nonzero there. [Weighted bound and field theorem](DedekindDiscriminant23DottieReading.lean) · [Exact Lean output](discriminant23-low-strip-replay-and-axioms.txt)

If $0<\operatorname{Re}w<1$, the pole-cleared reading for $L$ equals the pole-cleared reading for $\mathbb Q(\sqrt{-23})$ times the square of the character fold at the same $w$. If the quadratic field has its zeros on the line, Dedekind RH for $L$ is equivalent to the strip-zero statement for that one fold. If $|\operatorname{Im}w|\le7/6$, Lean bounds both factors away from zero and proves $\zeta_L(w)\ne0$ throughout the band. [Factor identity and wider band](discriminant23-dottie-field-reading.md) · [Exact Lean output](discriminant23-factor-reading-replay-and-axioms.txt)

If every Dirichlet character modulo $23$ has its strip zeros on the line, Lean supplies the quadratic base result. Then Dedekind RH for $L$ is equivalent to the character fold being nonzero throughout $1/2<\operatorname{Re}w<1$ and $|\operatorname{Im}w|>7/6$. [Modulus-23 theorem](DedekindDiscriminant23DirichletReduction.lean) · [Exact Lean output](discriminant23-dirichlet-mod23-replay-and-axioms.txt)

If I count zeros through height $T$ with their multiplicities, the count for $L$ is the count for the quadratic base plus twice the character-fold count. If the rational Dirichlet input at $23$ is supplied, Dedekind RH for $L$ is equivalent to the complete character count and its on-line count agreeing at arbitrarily high checkpoints. [Exact count and cofinal theorem](DedekindDiscriminant23ZeroCounts.lean) · [Lean output](discriminant23-zero-counts-replay-and-axioms.txt)

If I evaluate the character fold on the critical line at heights $5$ and $11/2$, Lean checks a positive reading at $5$ and a negative reading at $11/2$. So there is a common zero of the fold and $\zeta_L$ between those heights. The square of the fold gives the field zero multiplicity at least two. Replay with the same pinned tools and the `-CharacterBracket` switch. [Endpoint and multiplicity theorems](DedekindDiscriminant23CharacterBracket.lean) · [Lean output](discriminant23-character-bracket-replay-and-axioms.txt)

If $T\ge11/2$, the reflected points both enter the critical-line count through $|\operatorname{Im}w|\le T$. The fold contributes at least two and the splitting-field count is at least four, with multiplicities. [Reflection and cumulative lower bound](DedekindDiscriminant23CharacterReflectedCounts.lean)

## Complex values and derivatives for a general number field

If I truncate a field's folded Mellin integral at $R\ge1$ and widen the strip by $\rho>0$, Lean bounds the full complex error by $B_K(R,\rho)=2\int_R^\infty x^\rho|f_K(x)-f_{K,0}|\,dx$. If $0\le\operatorname{Re}w\le1$, the error in derivative order $n$ is at most $n!B_K(R,\rho)/\rho^n$. For each field and derivative order a sufficiently large cutoff meets any positive error allowance at every height. [Finite integral](ComplexMellinFoldEstimates.lean) · [Field tail](DedekindMixedThetaDerivative.lean) · [Uniform cutoff](DedekindMixedThetaMultiplicity.lean)

If the truncated slope with the exact pole correction clears that error at a zero, Lean gives vanishing order one for the actual Dedekind zeta. If I use the retained discriminant-$23$ theta polynomial, Lean gives error at most $1/100{,}000$ for the character value and first derivative throughout the closed critical strip. The complete count through $11/2$ now has three explicit signed bounds to fill. Replay with `-ComplexDerivatives`. [Multiplicity test](DedekindMixedThetaMultiplicity.lean) · [Exact error and count inputs](discriminant23-dottie-field-reading.md#complex-values-and-the-complete-count) · [Lean output](discriminant23-complex-derivatives-replay-and-axioms.txt)

## Five terms for the discriminant-$23$ character

If I subtract the theta series for $2x^2+xy+3y^2$ from the one for $x^2+xy+6y^2$, van der Blij's formula gives $2\eta(\tau)\eta(23\tau)$ at $q=e^{2\pi i\tau}$. The first five nonzero terms give $2(q-q^2-q^3+q^6+q^8)$, with the next term at degree 13. If I keep those five terms in the checked compact model, Lean bounds the change in the value and derivative by at most $1/20{,}000{,}000$ on the critical strip at every height. [Van der Blij's identity in Zagier](https://www.its.caltech.edu/~matilde/Zagier123ModularForms.pdf) · [Akbary and Totani, (1.9)](https://arxiv.org/abs/2408.00184) · [Five-term Lean theorem](DedekindDiscriminant23CharacterSparse.lean)

If $q=\exp(-\alpha e^u)$ with $\alpha=2\pi/\sqrt{23}$, each heat power gives $\int_0^\infty e^{wu}q^n\,du=(n\alpha)^{-w}\Gamma(w,n\alpha)$. The other half uses $1-w$. Ng uses incomplete gamma expansions for this family and records the first positive zero of the conductor-23 character factor at height approximately $5.1156833287$. The optional reference bracket uses the classical eta identity and outward integer arithmetic. [Incomplete gamma integral](https://dlmf.nist.gov/8.2.E2) · [Ng, Sections 4.3.3–4.3.5](https://www.cs.uleth.ca/~nathanng/RESEARCH/phd.thesis.pdf)

If I use 32 nine-point panels, Lean gives error at most $3/100{,}000$ for the value and derivative of the original compact model throughout $0\le\operatorname{Re}w\le1$, $|\operatorname{Im}w|\le11/2$. Combining shared endpoints gives 257 integration nodes. With the five-term reading, the new count theorem asks for three strict margins of $201/20{,}000{,}000$ and then gives two simple character zeros on the line. The exact integer replay clears these margins over 46 cells. Lean still takes the three inequalities as premises. Replay the Lean bounds with `-CharacterQuadrature`. Replay the integer calculation with `python check_character_fixed_bands.py DedekindDiscriminant23CharacterPolynomial.lean --sparse --reference-bracket`. [Quadrature rule](ComplexNewtonCotes.lean) · [Complex value and derivative](DedekindDiscriminant23CharacterPanel.lean) · [Integer replay](check_character_fixed_bands.py) · [Lean and integer output](discriminant23-character-quadrature-replay-and-axioms.txt)

## Two character zeros through height 5.5

I group the quadrature into 257 distinct samples, then use the same samples for the even value polynomial and the odd slope polynomial. Lean checks every sample box and 72 coefficient boxes. The original value and slope are within $33/10^6$ of their Taylor readings across $0\le\Re w\le1$, $|\Im w|\le11/2$. [Taylor error](DedekindDiscriminant23CharacterMoments.lean) · [Sample boxes](DedekindDiscriminant23AmplitudeData.lean) · [Coefficient boxes](DedekindDiscriminant23CoefficientData.lean)

If I keep 34 terms, the stored coefficient boxes bound the dropped terms by $40/10^6$. If the shorter readings clear $83/10^6$, the full Taylor readings clear $43/10^6$. All 46 rectangle comparisons pass with `decide +kernel`. The complete and critical-line character counts through $11/2$ are both 2. [Tail bound](DedekindDiscriminant23ReadingTail.lean) · [Exact count and premises](DedekindDiscriminant23CountCertificate.lean)

The squared character factor adds 4 to each count for the Galois field, above the count for the quadratic base. If I supply the critical-line theorem for the Dirichlet characters modulo 23, Dedekind RH for the Galois field is equivalent to excluding character zeros with $1/2<\Re w<1$ and $|\Im w|>11/2$. [Lean count and remaining strip](DedekindDiscriminant23CountCertificate.lean)

Run the pinned replay with `-CharacterCount` to check the samples, cells and count from source. [Replay and axiom output](discriminant23-character-count-replay-and-axioms.txt)

## Carry the count through height 6

I use the same 257 samples and coefficient rows in the next half-unit band. All 32 sign comparisons pass with `decide +kernel`. The retained real part is below $-600/10^6$, and the full approximation error is at most $548/10^6$. The character fold then has real part below $-52/10^6$ throughout $0\le\Re w\le1$, $11/2\le\Im w\le6$. Reflection covers the negative band. [Cell signs](DedekindDiscriminant23SixBandSigns.lean) · [Full error and count](DedekindDiscriminant23SixBand.lean)

The complete and critical-line character counts stay at 2 through $|\Im w|\le6$. Its square adds 4 to each count for the Galois field in addition to the quadratic-base count. If I supply the Dirichlet critical-line theorem modulo 23, the remaining character check is $1/2<\Re w\le31/32$, $|\Im w|>6$. [Exact premises](DedekindDiscriminant23SixBand.lean)

### The signed crossing through height 8

If my analytic reading is real on a vertical line, its real values have opposite signs at the ends, and the signed imaginary derivative stays positive across the rectangle, Lean gives one simple zero on that line. I can change the rectangle, the line, and the direction of the crossing. If the rest of the band is clear, the new zero and its reflection add 2 to the cumulative count. [Crossing theorem](ComplexStripSingleZero.lean) · [Count transfer](ComplexStripCrossingCount.lean)

I keep the 257 samples and take 54 of the stored terms. I use the radius of each sample in the exponential error and enlarge the quadrature circle to radius $1/2$. Lean gives a value and slope error of at most $14/10^6$ through height 8. The 35 rectangle comparisons clear $16/10^6$ with `decide +kernel`. I use the slope in the center and the value on both sides. [Error](DedekindDiscriminant23EightError.lean) · [Signs](DedekindDiscriminant23EightSigns.lean)

Lean gives one new positive simple zero between $13/2$ and $59/8$ on $\Re w=1/2$. The complete and critical-line character counts through $|\Im w|\le8$ are both 4. The squared character factor adds 8 to each Galois-field count over the quadratic base. If I supply the Dirichlet critical-line theorem modulo 23, the remaining check is $1/2<\Re w\le31/32$, $|\Im w|>8$. [Exact theorem and premises](DedekindDiscriminant23EightBand.lean) · [Lean output](discriminant23-eight-band-replay-and-axioms.txt)

## The same quadrature panels at every height

If I keep the two reflected exponentials as the integration weights, I can take Taylor coefficients of the theta density at the 32 fixed panel centers. I use 20 coefficients per panel. The input $w$ enters through integrals of a power times $e^{wu}$ or $e^{(1-w)u}$. Each integral follows from endpoint exponentials and the previous integral, with a power integral when the rate is zero. [Weighted Taylor bound](WeightedContourTaylor.lean) · [Exponential moments](ExponentialMoments.lean) · [Field formula](DedekindDiscriminant23PhaseEvaluation.lean)

If $0\le\Re w\le1$, the value and first derivative errors from quadrature are each at most $1/10^{10}$ for the finite theta model. Every omitted lattice norm is at least $33$. Keeping $23$ powers of the heat coordinate in the omission estimate gives the theta-model allowance $1/10^9$, including the integral beyond the cutoff. The combined bound for the actual character reading and its derivative is $11/10^{10}$ at every height. If I enclose the fixed coefficients once, Lean bounds how far those enclosures can shift each weighted panel. The coefficient error and the numerical error of the moments must also fit inside a sign margin. [Coefficient enclosures](WeightedContourTaylorEnclosures.lean) [Theta remainder](Discriminant23ThetaEnvelope.lean) · [Reading and derivative bounds](DedekindDiscriminant23PhaseQuadrature.lean) · [Replay and exact Lean output](discriminant23-phase-quadrature-replay-and-axioms.txt)

Replay this section with `-CharacterQuadrature`.

### Choose the cutoffs for any positive error tolerance

If I retain norms up to $N$ and choose $p\ge1$ with $18p+9\le13(N+1)$, the two lattice polynomials approximate the class-theta difference with error at most $16q^p$ for $0\le q\le3/11$. For a radial endpoint $R$, the assembled model allowance is $15(3/11)^{p-1}+(126/5)e^{-5R/4}$. [Lattice truncation](Discriminant23ThetaEnvelope.lean) · [Integrated error and derivatives](DedekindDiscriminant23CharacterComplex.lean)

I take $R=e^L$ and absorb the logarithmic Jacobian into the density. The two rates in the remaining weight are $w-1$ and $-w$. Their exponentials have norm at most one for $0\le\Re w\le1$ along the real integration interval. If I increase the Taylor depth by one, the quadrature allowance is halved. The moment formula uses the endpoint recursion on the reflected panel. [Exact moments and all-height bound](DedekindDiscriminant23AdaptivePhase.lean)

If I ask for any positive tolerance, Lean supplies one set of cutoffs and one Taylor depth for the value and slope together over the whole closed strip. The concrete choice $N=64$, $p=46$, $L=4$, and $96$ terms per panel gives an absolute error below $10^{-23}$ on all $16$ panels combined. For a sign test, the finite-sum enclosure must clear that allowance. [Lean theorem and replay](discriminant23-tunable-error-replay-and-axioms.txt)

For a positive rational tolerance $a/b$, I can choose the parameters using three integer inequalities. Lean proves that the inequalities can all be satisfied and that they imply the requested absolute error for both readings. [Integer parameter tests](DedekindDiscriminant23AdaptiveParameters.lean)

## Extend an existing count for any number field

If the complete count and the on-line count agree through $T$, a zero-free certificate on $1/2<\Re w\le31/32$, $T<|\Im w|\le U$ gives agreement through $U$. The field's right edge and reflection supply the rest of the strip. If I can supply such bands through arbitrarily large $U$, Lean gives Dedekind RH for that field. [Band theorem](DedekindHighRightAfterCount.lean) · [Cofinal theorem](DedekindPolynomialBand.lean)

For a rational disk inside the strip, I take coefficients from the finite Mellin reading with the pole term kept exact. The error allowance is the radial tail plus the geometric Taylor tail. If the lower real endpoint of the rotated constant term exceeds that allowance plus the weighted mass of the other coefficient boxes, Lean proves nonvanishing across the disk. [Analytic allowance](DedekindDiskTaylorError.lean) · [Integer margin](MellinFixedPolynomialDisk.lean) · [Weighted tail](MellinFixedTaylorTail.lean)

If I fix the radii and the clearance from the strip edges, Lean gives one Mellin cutoff and Taylor degree for any positive error target, at every allowed center height. The coefficient identity divides the $n$th derivative by $n!$. For the folded Mellin reading, this cancels the factorial in the coefficient error and leaves the weighted radial tail divided by $\rho^n$. [Uniform analytic allowance](DedekindDiskTaylorAccuracy.lean) · [Coefficient error](DedekindTaylorCoefficientError.lean)

For the $n$th coefficient at $c$, I integrate the two folded phases with weights $(\log x)^n$ and $(-\log x)^n$, then divide by $n!$. The two pole terms are $(-1)^n/c^{n+1}$ and $1/(1-c)^{n+1}$, both multiplied by the same theta constant and subtracted. If the outer disk stays in the strip, Lean identifies this formula with the coefficient in the disk test. The error is still the radial tail plus the Taylor tail. [Exact moment and disk bound](DedekindMellinMomentCoefficients.lean) · [Lean output](dedekind-mellin-moment-coefficients-replay-and-axioms.txt)

Replay these results with `-HigherPolynomialBands`. [Lean output and axiom checks](dedekind-polynomial-bands-replay-and-axioms.txt)

## Discriminant-23 ideal norms and class number

I use the cyclic step over $F=\mathbb Q(\sqrt{-23})$. If a nonidentity inertia element acts on the cubic roots, then all three roots reduce to one value $r$. The cubic coefficients give $3r=0$ and $3r^2=1$. Lean rules this out at every finite prime and gives $|\operatorname{disc}(L)|=23^3$. [Relative ramification](DedekindDiscriminant23Unramified.lean) · [Discriminants and completion](DedekindDiscriminant23Integers.lean)

Lean identifies the two forms in my disk formula with the element norm on the full ring of integers and with the element norm divided by $2$ on an ideal of norm $2$. Every ideal class has a representative of norm at most $3$. The ideals above $2$ and $3$ give exactly three classes, and Lean proves they are distinct. [Norm forms](DedekindDiscriminant23NormForms.lean) · [Class number](DedekindDiscriminant23ClassNumber.lean) · [Derivation and replay command](discriminant23-field-arithmetic.md) · [Exact Lean output](discriminant23-field-replay-and-axioms.txt)

## Discriminant-23 prime splitting and Euler product

If $\mathfrak p$ is a prime of $F$, the order of its class gives the residue degree of every prime above it in $L$. The principal class gives three primes of degree one. Either other class gives one prime of degree three. Lean gets this from the Hilbert class field identification and uses it to match all the Euler factors. [Hilbert class field and splitting](DedekindDiscriminant23Hilbert.lean)

If $\operatorname{Re} w>1$, the actual $\zeta_L(w)$ equals $\zeta_F(w)$ times the two nontrivial class-character series. Clearing the two poles lets Lean continue the completed product identity to the whole plane. The two nonprincipal classes give the same theta sum and the same kernel occurs on both halves of the fold. [Exact factorization](DedekindDiscriminant23EulerProduct.lean) · [Class kernels and continuation](discriminant23-dottie-field-reading.md)
