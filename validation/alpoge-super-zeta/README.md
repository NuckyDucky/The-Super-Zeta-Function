# Alpöge and Super Zeta

I start with my original squared-root sum after continuation, $Z$, and its entire Mellin correction, $J$. I use

$$
w=2s,\qquad A(s)=2\pi^{-2s}(2^{2s}-1),\qquad D(s)=Z(s)-J(s).
$$

The scale map $s\mapsto 2s$ is a global bijection. The original Super Zeta address $w\mapsto Z(w/2)$ has a separately proved inverse in $15/64\leq\Re(w/2)\leq17/64$, $\Im(w/2)\ge101$. It recovers the input for the quaternion comparisons. The ordinary zero test at that input uses $D$.

- **Ordinary RH and cumulative counts.** The determinant product and root-sum theorem establish $D(s)=A(s)\zeta(2s)$ from the spectrum. The series theorem uses $1/2<\Re s<1$. The continued zero test uses $0<\Re s<1/2$ and preserves the analytic order at $w=2s$. The cumulative route takes complete counts through cofinal checkpoints and equality with the on-line counts there. [Root sum and order](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/UnitSpectrum.lean#L30) · [Cumulative theorem](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/verification/quartic-kernel/source/QuarticHeightAssembly.lean#L51)
- **Dottie height selection.** The arrow and witness-band theorem concerns the marked return parameters and measuring region in $w$. The spectral zero correspondence works at any height in the strip. [Marked height](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/DottieMarkedHeight.lean#L168) · [Reversible chart](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/SuperZeta/QuarterLine/QuarticTurn.lean#L66)
- **Quartic bounds.** The exact factorization is $\zeta_K(w)=\zeta(w)\beta(w)G(w)$. The Dottie ring theorem takes the moment enclosures, signed remainder, and rational cofactor inputs. A separate full-strip reduction takes the cofactor line statements and upper-right nonvanishing of the Gaussian reading. [Exact ring premises](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/validation/dottie-score/ERH-breakdown.md) · [Full-strip reduction](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/ArchivedQuarticZeroTransport.lean#L70)

## What cancels

The logarithm of the relative determinant on the Mellin ray is $\log(1+(x/\cosh x)^2)$ at the unit coupling. Its Mellin term gives $J$. The entire continuation of $J$ is what subtraction removes. The residual part $D$ is supplied by the odd half-integer cosine reference. The residue $1/\pi$ at $s=1/2$ survives both before and after subtraction. [Original log determinant and integral](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/Reference.lean) · [Entire correction](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/MellinContinuation.lean#L206) · [SpectralBridge.lean](SpectralBridge.lean)

The two ordinary tests have different equations. In the open strip $Z(s)=J(s)$ iff $\zeta(2s)=0$. At a coincidence their common value is $J(s)$. A zero of $Z$ itself satisfies $J(s)=-A(s)\zeta(2s)$. A simultaneous zero of $Z$ and $J$ requires both equations.

Let $L_2$ be the trivial character's $L$-function mod two. Away from $2s=1$,

$$
D(s)=2\pi^{-2s}2^{2s}L_2(2s),\qquad L_2(w)=(1-2^{-w})\zeta(w).
$$

This is the Euler-factor removal in the change-of-level argument. The factors outside $L_2$ are nonzero. On $\Re s=0$, $Z(s)=J(s)$ precisely at $s=\pi ik/\log 2$, $k\in\mathbb Z$. Ordinary zeta is nonzero there by reflection to $\Re w=1$ and its value at zero. In the open strip, $A$ is nonzero and preserves the ordinary zero and its multiplicity. [Boundary and mod-two checks](OrdinaryInteractions.lean) · [Upstream Euler-factor argument](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L7)

The boundary coincidences are simple zeros of $D$ with

$$
D'(s)=4\log 2\,\pi^{-2s}\zeta(2s).
$$

At $s=0$ this slope is $-2\log 2$. At $s=0,-1,-2,\ldots$, the existing Mellin theorem gives $J(s)=0$. At $0$, $A$ vanishes. At the negative integers, $\zeta(2s)$ has its trivial zeros. Thus all three functions $Z$, $J$, and $D$ vanish at the nonpositive integers. [Contact orders and negative integers](ContactOrders.lean)

There is also an arithmetic integral for the *value* of $D/A$. Using the repository's existing fractional-part Mellin formula, in $\Re w>0$ with $\Im w\ne0$,

$$
\frac{D(w/2)}{A(w/2)}
=\frac{w}{w-1}-w\int_1^\infty \{x\}\,x^{-w-1}\,dx .
$$

An ordinary coincidence in that domain is therefore equivalent to equality of the fractional-part integral with $1/(w-1)$. The smoothed prime ramp below instead reads the *logarithmic derivative*. [Existing fractional-part integral](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/QuarterLine/QuarterEuler.lean) · [Checked adapter](ContactOrders.lean)

## Which weights cancel the Hurwitz pole

I use my archived residue grid and give each class $a\bmod N$ its own weight $c_a$. The reading on the same scale is

$$
H_c(s)=N^{-2s}\sum_{a\bmod N}c_a\,\zeta(2s,a/N).
$$

Lean identifies this with Mathlib's continuation of the weighted periodic Dirichlet series at $w=2s$. Taking the trivial character mod two recovers the original corrected spectrum with the known nonzero scale factor above. At $s=1/2$, the residue of $H_c$ is $\frac1{2N}\sum_a c_a$. If $\sum_a c_a=0$, the common Hurwitz pole cancels and $H_c$ is entire. This applies to every nontrivial Dirichlet character, whose weights sum to zero. If Alpöge's Dirichlet zero theorem is supplied, then the character-weighted reading's zeros in $0<\Re s<1/2$ lie on $\Re s=1/4$. The input in Lean is the exact published statement. [Archived unweighted grid](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return/ResidueAnchors.lean#L69) · [Pinned periodic continuation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L78) · [Lean port](ResidueGridPort.lean)

## What the two native Dottie words keep

If I compare the two rooted words at the archived absolute marks $-\pi/6$ and $+\pi/6$, I get two entire corrections with $J_-(1)=0$ and $J_+(1)=8/3$. Both continued spectra are $Z_\pm=R+J_\pm$ with the same $R(s)=\pi^{-2s}(3^{2s}-1)\zeta(2s)$. If I subtract the raw readings, I keep the difference of corrections. If I compare $J_-Z_+-J_+Z_-$, I get $(J_--J_+)R$ and keep the zero order wherever the corrections differ. The first-zero intervals give that separation at the same spectral input for both words. [Derivation and exact scope](native-contact.md) · [Lean replay](native-lean-audit.txt) · [Saved values and derivatives](native-zero-output.txt)

The second pass through Alpöge adds the weighted contour count, a good-height and prime-power window comparison, and the Artin-to-Hecke entry point for the Gaussian factor. [Exact declarations and inputs](alpoge-second-pass.md)

I used the weighted circle proof on $C=J_-Z_+-J_+Z_-$ around the same first zero. If the four central Mellin coefficients meet their enclosures, Lean gives $|J_--J_+|>11600$ on the closed disk. If the cross-product meets the residual and derivative bounds, Lean gives one simple zero with count $1$ and location $c+(2\pi i)^{-1}\oint (s-c)C'(s)/C(s)\,ds$. Reflection gives $\Re s=1/4$ exactly. The 256-bit replay supplies the numerical inputs and encloses the height in an interval of width $2\times10^{-24}$ on the spectral scale. [Proof and conventions](native-contour.md) · [Clean Lean audit](native-factor-contours-audit.txt) · [Interval output](native-contour-output.txt)

I certify that same cross-product through $H(s)=(1-2^{1-2s})\zeta(2s)$ and the original correction gap. Lean checks both finite eta comparisons and all 43,200 middle sample positions. The final theorem bounds the gap by $|J_--J_+|>11600$ on the closed disk, reads exactly one simple zero of $C$, and returns its exact location on $\Re s=1/4$. [Closed certificate](FirstDottieCrossCertificate.lean) · [Build and axiom audit](native-dottie-cross-audit.txt) · [Reproduce the proof](native-eta-contour.md)

For the Dedekind quartic, if the rational Dirichlet critical-line inputs are supplied, a hypothetical off-line zero of $\zeta_E$ forces the Gaussian factor to vanish at that same $w$. [Quartic reduction](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/ArchivedQuarticZeroTransport.lean#L70)

If I truncate each central Mellin coefficient to $[-32,5]$, Lean bounds the discarded part by $10^{-11}$. Lean also checks the exact 25-node rule and proves its panel error bound. The 192-bit Arb replay passes the eight finite inequalities used in the disk gap. [Mellin bounds and replay](native-mellin-quadrature.md) · [Fresh Lean audit](native-mellin-lean-audit.txt)

If $|\Im u|\le1/16$ on the logarithmic Mellin coordinate, Lean makes the normalized determinant ratio at most $2/3$ in norm. This supplies the Cauchy error bound for all 2,368 panels. Lean checks the eight weighted-sum comparisons, the 16,000 outer sample positions, and the 43,200 middle positions in 432 kernel batches. [Enclosures and replay](native-mellin-quadrature.md#checking-the-middle-samples-in-lean)

If the factors are nonzero on the circumference, I can subtract each factor's weighted contribution even when they share an interior zero. At the origin, Lean counts three for the cross-product, two for the corrections and one for the arithmetic prefactor. This leaves zero ordinary zeta zeros. The fixed-radius check uses $r=1/128$. [Exact subtraction and origin check](native-contour.md#removing-correction-zeros-from-the-count)

For the quartic, I used Alpöge's full weighted circle theorem on the continued equal-sign detector. If the detector identity and boundary nonvanishing hold and the detector is within $e<1024/31$ of a holomorphic approximation on the right circumference, Lean excludes Gaussian zeros throughout that disk and its same-height mirror. [Quartic contour theorem and exact inputs](quartic-contour.md). The relative residual form proves the required boundary nonvanishing from that same bound. [Lean field theorem](QuarticContourResidual.lean)

## Connections through the upstream proofs

The [import summary](upstream-summary.json) covers two import edges from each named root. The [analytic import closure](upstream-analytic-closures.json) gives the dependencies for the selected pole and window modules. These traces cover import headers. The entries below refer to declarations inspected in the pinned source.

| Route | Upstream declaration | Super Zeta input and result |
| --- | --- | --- |
| Reflection and nonvanishing | [Formalism.VW.rh_of_right](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean) takes right-side ordinary nonvanishing away from 1. The [headline projections](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Supplements/Kernels/MainTheorems.lean) use the all-character theorem. | The normalized difference obeys zeta's reflection at $1/2-s$ and has the same-height zero reflection $1/2-\bar s$. The imported proof gives full Mathlib RH iff $D(s)\ne0$ at $\Re s>1/4$, $2s\ne1$. [Lean adapter](AlpogeAdapters.lean) |
| Character decomposition | [Claim.prim_zero and Claim.prim_reflect](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean) remove Euler factors and use primitive completion. | The odd cosine reference already gives the trivial character mod two. The mod-three angular slope picks out $\chi_{-3}$ through the difference of the $1/3$ and $2/3$ Hurwitz readings. The arbitrary-modulus port specifies the weights and continuation. Finding which marked dynamical readings realize those weights is a separate question for each character. [Mod-three angular construction](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-20-liu-angular-velocity-v001/README.md) · [Arbitrary-modulus port](ResidueGridPort.lean) |
| Pole and residue | [Deduction.logDeriv_local](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LogDerivLocal.lean#L9) reads a zero's order as a residue. [Deduction.poleData_abstract](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L22) uses an entire $g$ with $g(1)\ne0$. | $D$ retains its residue $1/\pi$ and its analytic orders in the strip. The actual Gaussian factor meets the endpoint hypothesis because $\beta(1)G(1)=\operatorname{Res}_{w=1}\zeta_K(w)$, as proved from the class-number limit. [Endpoint proof](GaussianEndpoint.lean) |
| Prime powers | [Deduction.ramp and Deduction.Gchi](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean) use von Mangoldt weights and explicit endpoint corrections. [Euler-factor derivative bound](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/EulerFactorLogDerivBound.lean) controls the change at one prime when $\Re w>1$. | In $\Re(2s)>1$, $(A'/A-D'/D)/2=\sum_n\Lambda(n)n^{-2s}$. Keeping $1-2^{-w}$ in the channel excludes the powers of 2. Its derivative and the elementary scale term must be tracked when switching between the two formulas. [Prime-power check](OrdinaryInteractions.lean) |
| Smoothing and signed comparison | [Modulus-one ramp](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiModOne.lean#L115) and [general weighted ramp](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean#L65) give Mellin identities. [Formalism.OCStep](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Formalism/StatementOC.lean#L23) is a proposition about a one-sided bound and equality of orders. | Substitute $w=2s$ in the ramp and compare it with a nontrivial character at the same input. Equal-order poles can cancel in the difference. In the earlier positive weighted sum the orders add. Each operation yields a different test. [Mellin adapter source](SpectralMellin.lean) |
| Counts | Pinned Mathlib gives `IsCompact.inter_riemannZetaZeros_finite`. The upstream [headline proof](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Main.lean) uses right-half-plane and reflection arguments for its line conclusion. | Doubling takes a compact set of coincidences in the strip to a finite subset of ordinary zeros. The existing order theorem preserves the weight of each point. The cumulative count theorem has its own completeness and cofinality hypotheses. [Finite-set check](OrdinaryInteractions.lean) |
| Signed windows | [Deduction.landau_window](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83) takes `PoleData` and a one-sided bound on arbitrarily late arithmetic windows. [zeroFreeAll_of_topG](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean) uses rational character host conditions. | For $G$, the candidate smoothed residue at a zero $\rho$ of order $m$ is $-m/[\rho(\rho-1)]$. This normalization differs from the archive's equal-sign detector, of residue $-m/2$. The next inputs are the actual prime-ideal weights and transform and the window bound. The real-pole sign follows from the checked quartic endpoint and positivity of the Dedekind series to its right. Here the window variable is $\log x$, while the Dottie selection concerns $\Im w$. [Existing detector](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/GaussianPrimeResidue.lean#L35) · [Gaussian adapter source](GaussianPolePort.lean) |

## Recovering the orders from the two rooted phases

If the two zero orders are $m,n$, the ordinary signed residue reads $(m-n)/2$. I take the actual `-+` and `+-` returns from cap $1$ and use their outputs $a,b$ as weights before subtraction. Then the residue is $(am-bn)/2$. Exchanging the two phase weights and subtracting the results reads $(a-b)(m+n)/2$. Lean proves $a\ne b$ on the imaginary lift $L=iy$, $0<y<\pi/2$, and checks recovery against the principal character mod two, where the two orders agree everywhere in the strip. [Order comparison and exact control](ordered-contact.md)

## Same-input field test

`quartic_chart_of_dirichlet` takes `hD : DirichletLZerosOnLine`, the exact published Dirichlet statement. Its moduli one and four supply the $\zeta$ and $\beta$ cofactors. At an off-line input in the proved address chart, with any paint in the $b$ slot of $Q_{\mathbb H}=a+bj$, the Lean theorem gives

$$
Z(w/2)\ne J(w/2),\qquad
\zeta_K(w)=0\ \Longleftrightarrow\ jQ_{\mathbb H}k=kQ_{\mathbb H}j.
$$

At $\Re w>0$, $w\ne1$ and away from all factor zeros, the Gaussian logarithmic derivative is the field logarithmic derivative minus the $\beta$ logarithmic derivative and the logarithmic derivative of $(D/A)(w/2)$ with respect to $w$. At a candidate zero the associated pole calculation uses a punctured neighborhood. [AlpogeAdapters.lean](AlpogeAdapters.lean) · [Original chart and paint theorem](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/ArchivedQuarticSpectralAddress.lean#L55)

## Research questions with precise inputs

1. **Ordinary contacts and order.** The new boundary calculation explains an entire family of coincidences that persist even though $\zeta(2s)$ stays nonzero there. For the ordinary critical strip the exact next local observable is $J(s)$ at the coincidence, or its derivatives if both values vanish. The independent cumulative route takes the `cofinal`, `complete`, and `counts` premises in the [original Lean statement](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/verification/quartic-kernel/source/QuarticHeightAssembly.lean#L51).
2. **Characters and cancellation.** The finite arithmetic grid now identifies the reading for every character. The next dynamical input for a selected character is an ordered return or angular observable whose coefficients are the required weights, as for the modulus-three reading. At a common input the signed slope has principal part $(m_\zeta-m_\chi)/(2(z-s))$, with both orders at $w=2s$. Equal orders cancel in this comparison. A positive weighted sum instead adds orders. A zero-exclusion consequence of a signed window needs an estimate in the normalization of that comparison. [Residue grid](ResidueGridPort.lean) · [Mellin comparison](SpectralMellin.lean) · [Local pole comparison](SignedContact.lean)
3. **Arithmetic windows.** I apply the imported `Deduction.landau_window` to the same Gaussian factor used by the quaternion comparison. If the ramp supplies the inputs printed in `quartic_rh_of_gaussian_ramp`, and the Dirichlet theorem supplies the two rational cofactors, then Lean gives `DedekindZetaRH K` for the archived quartic. The ramp is a real function of $u=\log x$, anchored at $G'(1)/G(1)$. The prime-power weights to check against the actual field Euler factors are

   $$
   a(p^k)=
     \sum_{\substack{\mathfrak p\mid p\\ f_{\mathfrak p}\mid k}}
        f_{\mathfrak p}\,\chi_G(\mathfrak p)^{k/f_{\mathfrak p}},
   $$

   with residue degree $f_{\mathfrak p}$ and ramified factors included according to their Euler factor. The first arithmetic identity is $-G'(w)/G(w)=\sum_n a(n)\Lambda(n)n^{-w}$ for $\Re w>1$. The weighted Mellin ramp can use this series once the identity and absolute summability are available. The generic criterion then takes measurability, exponential growth in $u$, the Laplace identity, and the window inequality. The quartic proof supplies the real-pole condition from the positive ideal series above one and the class-number residue at one. [Checked real-pole theorem](GaussianRealPoles.lean) · [Build and axioms](quartic-residual-audit.txt) [Signed norm coefficients](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/GaussianPrimePowerCoefficients.lean) · [Window implication](GaussianWindowPort.lean) · [Exact ring premises](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/validation/dottie-score/ERH-breakdown.md)

## Revisions and audit evidence

- Super Zeta `eaa526828cf700a2f43aeeb1c81de4309be5afee`. [Source](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/eaa526828cf700a2f43aeeb1c81de4309be5afee)
- Alpöge `ba2a065656ec7c638baa601994de3e0245ff6665`. The original `RhOfRight` and `Statements` sources were replayed locally. The all-character result is an explicit adapter input, with a separate independent upstream verification. [Source](https://github.com/Deicyde/riemann-hypothesis/tree/ba2a065656ec7c638baa601994de3e0245ff6665) · [Local replay](upstream-build.txt) · [Independent verification](https://math.mit.edu/~drew/grh/#what-was-verified)
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Lean 4.33.1, `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. [Mathlib pin](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
- [Local Lean output](lean-audit.txt) includes exit codes and transitive axioms for the new adapters. [Upstream replay](upstream-replay.txt) records the unchanged local import closure. The listed axiom set is `[propext, Classical.choice, Quot.sound]`.

## Gaussian prime-window verification

If I use the original Euler weights, Lean identifies the logarithmic derivative of the Gaussian factor. If `hD` and the prime-only `hcut` hold, Lean gives `DedekindZetaRH QuarticModel.K`. The recorded arithmetic now includes the odd and even prime powers, the finite window checks, and the exact cutoff condition for the quartic. [Lean proofs, replay and remaining bound](gaussian-prime-windows/README.md)

## Replay

Build the original `lean-ideal73` package at the Super Zeta pin, and make sure the pinned Mathlib packages have their compiled libraries. From this packet's directory, stage the 28 required upstream files directly from the Alpöge Git objects, then replay the adapters with your local toolchain and library paths.

```powershell
python .\trace_upstream.py --upstream $alpogeCheckout --stage-analytic
.\replay.ps1 -LeanExecutable $leanBinary -SuperZetaLibrary $superZetaLibrary -MathlibPackages $mathlibPackages
```

`$superZetaLibrary` is the `lean-ideal73/.lake/build/lib/lean` directory. `$mathlibPackages` is the built `.lake/packages` directory. Use its physical path if a Windows junction would exceed the path limit. The replay builds the upstream closure in import order and the local modules with warnings treated as errors. [Pinned-source staging](trace_upstream.py) · [Replay script](replay.ps1)
