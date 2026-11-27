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

## Discriminant-23 ideal norms and class number

I use the cyclic step over $F=\mathbb Q(\sqrt{-23})$. If a nonidentity inertia element acts on the cubic roots, then all three roots reduce to one value $r$. The cubic coefficients give $3r=0$ and $3r^2=1$. Lean rules this out at every finite prime and gives $|\operatorname{disc}(L)|=23^3$. [Relative ramification](DedekindDiscriminant23Unramified.lean) · [Discriminants and completion](DedekindDiscriminant23Integers.lean)

Lean identifies the two forms in my disk formula with the element norm on the full ring of integers and with the element norm divided by $2$ on an ideal of norm $2$. Every ideal class has a representative of norm at most $3$. The ideals above $2$ and $3$ give exactly three classes, and Lean proves they are distinct. [Norm forms](DedekindDiscriminant23NormForms.lean) · [Class number](DedekindDiscriminant23ClassNumber.lean) · [Derivation and replay command](discriminant23-field-arithmetic.md) · [Exact Lean output](discriminant23-field-replay-and-axioms.txt)

## Discriminant-23 prime splitting and Euler product

If $\mathfrak p$ is a prime of $F$, the order of its class gives the residue degree of every prime above it in $L$. The principal class gives three primes of degree one. Either other class gives one prime of degree three. Lean gets this from the Hilbert class field identification and uses it to match all the Euler factors. [Hilbert class field and splitting](DedekindDiscriminant23Hilbert.lean)

If $\operatorname{Re} w>1$, the actual $\zeta_L(w)$ equals $\zeta_F(w)$ times the two nontrivial class-character series. Clearing the two poles lets Lean continue the completed product identity to the whole plane. The two nonprincipal classes give the same theta sum and the same kernel occurs on both halves of the fold. [Exact factorization](DedekindDiscriminant23EulerProduct.lean) · [Class kernels and continuation](discriminant23-dottie-field-reading.md)
