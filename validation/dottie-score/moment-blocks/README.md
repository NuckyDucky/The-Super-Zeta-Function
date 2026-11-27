# Dottie moment blocks

If the projected reference value is at most $3167097610287262088/2^{64}$ and the eleven sharp moment boxes fit, Lean gives the signed bound of $-190.37(\Re w-1/2)S_0$ for the sharp prefix around the original right measuring circle. A direct reference estimate can supply this one scalar. The six reference moment checks also give that estimate. [Projection theorem](DottieSharpReferenceProjection.lean#L11) · [Axiom output](DottieSharpReferenceProjection.audit.txt) · [Moment route](../../../lean-ideal73/DottieMomentArchiveScores.lean#L21)

- **Reference prefix through 276,824,064.** Lean checked both integer components at degrees 0 through 5 for the first 128 off-diagonal pairs of zero-based row 11,763. [Lean source](DottieReferenceMomentBlock.lean) · [Axiom output](DottieReferenceMomentBlock.audit.txt)
- **Sharp prefix through 1,442,840,576.** Lean checked both integer components at degrees 0 through 10 for the first 32 off-diagonal pairs of zero-based row 26,858. [Lean source](DottieSharpMomentBlock.lean) · [Axiom output](DottieSharpMomentBlock.audit.txt)

These blocks contribute to the full row sums through `dottiePairRowBlock_add`. The signed circle theorem takes the full sharp score fits and the reference scalar. [Row addition](../../../lean-ideal73/DottieSymmetricChunks.lean#L31) · [Field inputs](../ERH-breakdown.md)

## Direct reference expression

At $w_0=1/2+i(T_D-1/512)$ let $t_0=\operatorname{Im}(w_0)$ and let $\phi$ be the phase of the completion factor there. The reference projection is exactly

$$
\left|\sum_{n=1}^{276824064}\frac{a_n}{\sqrt n}\cos(\phi-t_0\log n)\right|,
$$

with the original signed Gaussian coefficients $a_n$. Evaluating the sine and cosine at the phase endpoints gives the upper bound $0.1716868$ from the six enclosed reference moments. The sharp-circle theorem accepts the exact decimal $0.171687$ and the eleven sharp score fits. The directed replay of the archived full moment table gives an upper bound below $0.17168626$ at both 224 and 320 bits. The Lean proof keeps the six full moment enclosures explicit. [Exact formula](DottieDirectReference.lean#L43) · [Decimal comparison](DottieDirectReference.lean#L148) · [Lean audit](DottieDirectReference.audit.txt) · [Archived moments](../../../archive/2026-11-21-gaussian-rectangle-v001/signed-blocks.json)

To replay, build the pinned `lean-ideal73` imports as described in the [verification package](../../../lean-ideal73/README.md). From `lean-ideal73`, check each source with Lean 4.33.1 and the built imports on the module path.

```text
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottieSharpReferenceProjection.olean ../validation/dottie-score/moment-blocks/DottieSharpReferenceProjection.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieDirectReference.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieReferenceMomentBlock.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieSharpMomentBlock.lean
```
