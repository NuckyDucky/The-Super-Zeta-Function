# Dottie moment blocks

If the projected reference value is at most $3167097610287262088/2^{64}$ and the eleven sharp moment boxes fit, Lean gives the signed bound of $-190.37(\Re w-1/2)S_0$ for the sharp prefix around the original right measuring circle. A direct reference estimate can supply this one scalar. The six reference moment checks also give that estimate. [Projection theorem](DottieSharpReferenceProjection.lean#L11) · [Axiom output](DottieSharpReferenceProjection.audit.txt) · [Moment route](../../../lean-ideal73/DottieMomentArchiveScores.lean#L21)

- **Reference prefix through 276,824,064.** Lean checked both integer components at degrees 0 through 5 for the first 128 off-diagonal pairs of zero-based row 11,763. [Lean source](DottieReferenceMomentBlock.lean) · [Axiom output](DottieReferenceMomentBlock.audit.txt)
- **Sharp prefix through 1,442,840,576.** Lean checked both integer components at degrees 0 through 10 for the first 32 off-diagonal pairs of zero-based row 26,858. [Lean source](DottieSharpMomentBlock.lean) · [Axiom output](DottieSharpMomentBlock.audit.txt)

These blocks contribute to the full row sums through `dottiePairRowBlock_add`. The signed circle theorem takes the full sharp score fits and the reference scalar. [Row addition](../../../lean-ideal73/DottieSymmetricChunks.lean#L31) · [Field inputs](../ERH-breakdown.md)

To replay, build the pinned `lean-ideal73` imports as described in the [verification package](../../../lean-ideal73/README.md). From `lean-ideal73`, check each source with Lean 4.33.1 and the built imports on the module path.

```text
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieSharpReferenceProjection.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieReferenceMomentBlock.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieSharpMomentBlock.lean
```
