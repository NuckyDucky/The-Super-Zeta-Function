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

## One integer reference score

Lean encloses the phase at the original reference input within $5\times10^{-13}$ radians of $3.92292489981824$. If $S$ is the signed integer total over the original cutoff, the full reference projection differs from $|S|/2^{256}$ by at most $0.00000033276$. The comparison $10^7|S|\le1716866\cdot 2^{256}$ supplies the reference bound $0.171687$. [Phase theorem](DottiePreciseReferencePhase.lean#L93) · [Score theorem](DottieDirectReferenceScore.lean#L273) · [Axiom audits](DottieDirectReferenceScore.audit.txt)

The four-part integer calculation covered all 16,638 consecutive rows. Its normalized total was $0.171683928012601107\ldots$. Lean checked the integer comparison for this candidate and replayed both the final row and the full 11,763-pair interior row. Supplying the full equality of the Lean score and the recorded integer gives the decimal bound. [Candidate and exact remaining premise](DottieDirectReferenceCandidate.lean) · [Candidate receipt](DottieDirectReferenceCandidate.json) · [Full checked row](DottieDirectReferenceInteriorRow.lean#L74) · [Row audit](DottieDirectReferenceInteriorRow.audit.txt)

The [integer calculator](replay_direct_reference_candidates.py) takes a zero-based start row, an exclusive end row, and a destination for the row totals. The four partition boundaries are `0, 7373, 10426, 12868, 16638`.

To replay, build the pinned `lean-ideal73` imports as described in the [verification package](../../../lean-ideal73/README.md). From `lean-ideal73`, check each source with Lean 4.33.1 and the built imports on the module path.

```text
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottieSharpReferenceProjection.olean ../validation/dottie-score/moment-blocks/DottieSharpReferenceProjection.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottieDirectReference.olean ../validation/dottie-score/moment-blocks/DottieDirectReference.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottiePreciseReferencePhase.olean ../validation/dottie-score/moment-blocks/DottiePreciseReferencePhase.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottieDirectReferenceScore.olean ../validation/dottie-score/moment-blocks/DottieDirectReferenceScore.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieDirectReferenceBlocks.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieDirectReferenceCandidate.lean
lake env lean -j1 -s65536 -M5100 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieDirectReferenceInteriorRow.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieReferenceMomentBlock.lean
lake env lean -j1 -s65536 -M4500 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieSharpMomentBlock.lean
```

## Kernel replay with integer phase reduction

Lean checks that a single integer remainder gives exactly the old rounded weight at every norm in the prefix. The full score equals the original score. The one-worker replay of the same 11,763-pair row took 62.527 seconds, down from 134.279 seconds with the rational phase calculation. An independent source replay matched the exact row total and the three transitive axiom reports. [Weight and score identities](DottieFastReferenceScore.lean#L136) · [Axioms](DottieFastReferenceScore.audit.txt) · [Old timing](DottieDirectReferenceInteriorRow.audit.txt) · [New row and timing](DottieFastReferenceInteriorRow.audit.txt)

The batch generator checks the first 32 rows, row 1024, and the last two rows using the same weights. The row ranges here are zero-based with an exclusive end. Each source supplies an exact subtotal checked with `decide +kernel`. When an archived packed witness is available, Lean checks it again for the new weight. The full score equality with the candidate remains the reference proof input. [Generator](generate_fast_reference_replay.py) · [First 32 rows](DottieFastReferenceRows0To32.audit.txt) · [Row 1024](DottieFastReferenceRows1024To1025.audit.txt) · [Last two rows](DottieFastReferenceRows16636To16638.audit.txt)

From `lean-ideal73`, after building `DottieDirectReferenceScore`, run the fast-score build and a batch replay.

```text
lake env lean -j1 -s65536 -M5100 -DwarningAsError=true --root=../validation/dottie-score/moment-blocks -o .lake/build/lib/lean/DottieFastReferenceScore.olean ../validation/dottie-score/moment-blocks/DottieFastReferenceScore.lean
lake env lean -j1 -s65536 -M5100 -DwarningAsError=true ../validation/dottie-score/moment-blocks/DottieFastReferenceRows0To32.lean
```

From the packet directory, `python generate_fast_reference_replay.py 0 32 generated` generates the same first batch. Pass `--witness-root` for archived packed rows and `--checkpoint` for saved candidate totals.
