# ERH proof inputs

I keep the trial point $w$ fixed through the Super Zeta address and its inverse. The Lean 4.33.1 audit prints the theorem types for the original ring, the full strip for the quartic, and the arbitrary-number-field argument. The audit exited `0` and checked the transitive axioms of all seven declarations against `propext`, `Classical.choice`, and `Quot.sound`. [Lean source](DottieERHCloseoutAudit.lean) · [Actual Lean output](DottieERHCloseoutAudit.audit.txt)

## The original Dottie ring

The exact reference score and the three retained-band certificates are already used by `dottieProductionRightNonzero_of_tight_signed`. It takes `hw : w ∈ archivedDottieRightRing` and accepts any `ink : ℂ → ℂ`. These are its remaining bounds and factor inputs. [Field theorem](DottieProductionField.lean#L13)

| Premise | Exact condition |
| --- | --- |
| `hsharp` | For every `k < 11`, `(archivedScoredMomentBox dottiePrefixEnd k).fits (fixedSharpInput k) = true`. The cutoff `dottiePrefixEnd` is `1442840576`. |
| `href` | For every `k < 6`, `(archivedScoredMomentBox 276824064 k).fits (fixedReferenceInput k) = true`. |
| `hsigned` | For every `z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048)`, `(dottieOmittedSharpBlock z + dottieShorterMiddleSmooth z).im ≤ (188889 / 1000) * ((z.re - 1 / 2) * dottieCircleReference)`. |
| `hR` | `riemannZeta w ≠ 0` at the recovered point. |
| `hB` | `FieldCoefficientTransfer.chi4.LFunction w ≠ 0` at that same point. |

If those inputs hold, then `archivedQuarticZeta w ≠ 0`. The restart point is the two sets of moment boxes and the joint signed bound `hsigned` on the original circle. Keep the cofactor checks at the recovered $w$. [Reference and tail bounds](DottieProductionReferenceTight.lean)

## The same quartic over the full strip

`archivedQuarticRH_iff_upper_right` gives three conditions for `DedekindZetaRH QuarticModel.K`.

- `FieldTarget.StripZerosOnLine riemannZeta`.
- `FieldTarget.StripZerosOnLine FieldCoefficientTransfer.chi4.LFunction`.
- `∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → 0 ≤ w.im → archivedMellin w ≠ 0`.

The signed patch route takes the two strip results and `certificate : StripCover.HasSignedPatchBounds archivedMellin`. For **each** `n : ℕ`, give finitely many input patches covering `StripCover.rightBox n`. On each patch's intersection with that box, use a single unit direction $d$ and a positive patch margin $m$ with $m\le\Re(\overline d\,\mathrm{archivedMellin}(w))$ at every point in the intersection. Lean proves the boxes exhaust the right half of the strip. [Quartic reduction](../../lean-ideal73/ArchivedQuarticZeroTransport.lean#L70) · [Signed patch theorem](../../lean-ideal73/ArchivedQuarticSignedPatchCover.lean#L96) · [Box exhaustion](../../lean-ideal73/StripCover.lean#L28)

The marked height theorem takes `hre` in $[1/2+1/2048,\,1/2+63/2048]$, `him` with $\Im w+1/512\in[T_D-10^8,\,T_D+10^8]$, and `hmarked`. The last premise supplies `MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right)` for some $P,Q$ for both values of `right : Bool` and every `x ∈ Set.Icc (archivedDottieFlank - dottieFlankWidth) (archivedDottieFlank + dottieFlankWidth)`. The theorem places the original $w$ in the selected disk and gives the two marked period-640 returns. [Marked height theorem](../../lean-ideal73/DottieMarkedHeight.lean#L168)

## Arbitrary number fields

For an arbitrary number field $K$, `dedekindZetaRH_of_same_input_signed_gap` takes a continuation `Z`, readings `U` and `V`, and a family of regions indexed by `a : Orbit`. `axis a` is a complex coefficient for the region. `retained a w` is its retained contribution, and `main a w` and `tail a w` are real bounds. [Generic ERH theorem](../../lean-ideal73/DedekindDottieSetup.lean#L23)

| Premise | Exact condition |
| --- | --- |
| `hZ` | `IsDedekindZeta K Z`. In Lean, `Z` is differentiable over $\mathbb C$ off $1$ and agrees with `NumberField.dedekindZeta K` on $\Re w>1$. |
| `hzero` | For every $w$ in $0<\Re w<1$, `Z w = 0` implies `U w = V w`. |
| `hreflect` | For every $w$ in $0<\Re w<1$, `Z w = 0` implies `Z (1 - conj w) = 0`. |
| `hlocate` | For every $w$ in $1/2<\Re w<1$, `Z w = 0` implies `∃ a : Orbit, w ∈ region a`. |
| `hgap` | For every `a` and `w ∈ region a`, `tail a w < main a w`. |
| `hmodel` | For every `a` and `w ∈ region a`, `(retained a w).im ≤ -(main a w)`. |
| `htail` | For every `a` and `w ∈ region a`, `(axis a * (U w - V w) - retained a w).im ≤ tail a w`. |

If these premises hold for $K$, Lean gives `DedekindZetaRH K`. For the general ERH statement the construction and premises have to hold for every number field. [Definition and exact theorem types in Lean's output](DottieERHCloseoutAudit.audit.txt#L61)

## Replay the audit

Build the [Dottie score and field assembly](README.md#188889-signed-units-on-the-dottie-circle) with the pinned Lean and mathlib. Put its compiled modules and the `lean-ideal73` builds containing `ArchivedQuarticSignedPatchCover` and `DottieHeightVerification` on `LEAN_PATH`. From this directory run:

```sh
lean -j1 -s65536 -DwarningAsError=true DottieERHCloseoutAudit.lean
```
