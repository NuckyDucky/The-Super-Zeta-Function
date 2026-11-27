# Feed the candidate height into Dottie

Take a hypothetical zero $\rho$ with $1/2<\Re\rho\le127/128$. Put $t=\Im\rho$ and use reference height $t+1/512$. Lean supplies a dyadic Dottie disk $D_n(t)$ containing that exact input. If $F(\rho)=0$, every holomorphic weight $W$ has a point $z\in\partial D_n(t)$ where $\Im(W(z)F(z))\ge0$. This gives the same test for ordinary zeta and the completed mixed-theta reading of any number field. The Dottie centerline uses Baker and Rippon’s antiholomorphic half-step. [Candidate theorem](DottieCandidateCircles.lean) · [Dottie and Baker–Rippon](../../../docs/proofs/reciprocal-constructions.md#L175) · [Original half-step](https://doi.org/10.1080/17476938908814364)

## Compare the disks at the same height

Alpöge’s original near-one disk has center $\sigma+it$ and radius $1/2$. The large-height proof takes $t$ from a candidate zero and chooses $\sigma=1+1/(10000\log(|t|+2))$. For any $\sigma\ge1$, our exact fit criterion is

$$
D_n(t)\subseteq\overline B(\sigma+it,1/2)
\quad\Longleftrightarrow\quad
\sigma-1\le 2^{-n}/128.
$$

If $1<\sigma\le2$, $|t|\ge3$, and the disk fits, Lean applies Alpöge’s actual theorem to every $w\in D_n(t)$ and gives $|\zeta(w)|\le6(|t|+2)$. The fixed Cayley disk at $t=100000001$ gives $600000018$. The full-half-plane growth theorem separately gives the Cauchy majorant $10^9$ on the radius-$1/2$ disk centered at $3/4+100000001i$. [Containment](DottieNearOneDisk.lean) · [Exact transfer](DottieAlpogeDisk.lean) · [Original disk bound](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607/src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L42) · [Original candidate argument](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607/src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoNegReLeNorm.lean#L14)

The readable GRH proof starts from a candidate $\rho$, chooses $1/2<\beta<\Re\rho$, and uses a quadratic twist on the region $\Re s\ge\beta$, $|\Im s|\le|\Im\rho|$. Its near-one Cauchy estimates bound derivatives of regularized $L$-functions. The compact proof uses a prime-error bound and a Taylor convergence step after removing a pole. The 96 angular readings and the signed boundary test belong to the Dottie calculation. [Readable zero criterion](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean#L37) · [Readable Cauchy estimate](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean#L364) · [Compact zero argument](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L149)

## Keep the ordered corrections

The two native words give $Z_\pm(s)=R(s)+J_\pm(s)$ at $s=w/2$, with $R(s)=\pi^{-w}(3^w-1)\zeta(w)$. If I use each word’s own correction, the two corrected readings agree. Lean gives $|R(w/2)|\le24(|t|+2)$ under the disk hypotheses. If I subtract the raw readings, I get $J_+-J_-$. If I cross-multiply with the corrections, I get $(J_--J_+)R$. The cross-product keeps the ordinary zero order wherever $J_-\ne J_+$. [Native word identities](../../alpoge-super-zeta/NativeDottieContact.lean) · [First disk correction gap](../../alpoge-super-zeta/FirstDottieCrossCertificate.lean) · [Word transfer](DottieNativeCandidate.lean)

The `hCorrected` premise in the 4.35.0 replay is the word identity checked in the 4.19.0 native packet. Given that identity and an ordinary zero, Lean finds a **single boundary point** where both corrected words have nonnegative weighted imaginary part. A strict negative sign on the whole circumference for either corrected word would contradict the zero.

### Return to the shared boundary point

Keep this result for a dedicated follow-up. Lean chooses the scale first. For each holomorphic weight it then chooses one boundary point that works for both words. Check which larger families of ordered words have a common corrected reading. For the two raw words, test whether the gap $J_--J_+$ stays away from zero on higher Dottie disks, using the first-disk proof as the starting case. [Printed theorem](alpoge-dottie-replay.txt) · [First disk](../../alpoge-super-zeta/FirstDottieCrossCertificate.lean)

## Reproduce the circle test

If the 96 sample values each have error at most $10^{-12}$, Lean gives a uniform error at most $10^{-9}$ for the degree-64 polynomial on the fixed Cayley disk. The zero-exclusion theorem takes the sample enclosures and the signed polynomial arc bounds as inputs. The external `--ordinary` interval run gives $-\Im\zeta>1/16$ around the full circle with a certified lower bound above $0.08330$. It uses 70 closed intervals and the $10^{-9}$ allowance. [Lean sample theorem](DottieCayleyGrowthBridge.lean) · [Interval output](ordinary-circle-interval-audit.txt) · [Build and axiom output](alpoge-dottie-replay.txt)

First run [the sampled contour replay](README.md#replay) with `-SampledContours`. Point `AlpogeSource` to an unpacked checkout of the [original source mirror](https://github.com/homeowmorphism/riemann-hypothesis-original/tree/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607). The companion checks the five source hashes, expands two predicate aliases, updates the conditional simplifier name and rebuilds the needed declarations on the pinned toolchain.

```powershell
pwsh ./replay-alpoge-dottie.ps1 -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin> -AlpogeSource <original-checkout>
uv run --with python-flint==0.9.0 check-completed-circle.py --ordinary
```
