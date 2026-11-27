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

The refactored check now gives one exact subtotal for the first 80 consecutive rows of the original weight. Its imports cover `[0,32)`, `[32,56)`, and `[56,80)`. Smaller independent sources keep the interpreter within the memory cap. Compile those three sources to objects on the module path before checking the combined theorem. [Prefix theorem](DottieFastReferencePrefix80.lean#L15) · [Axiom audit](DottieFastReferencePrefix80.audit.txt)

## Join the checked ranges

The first 144 consecutive rows now have one checked subtotal for the original weight. The generator can reuse packed witnesses from either archived single rows or bundled rows. The assembler takes the source files for consecutive spans and generates a theorem that imports those exact certificates. It rejects a gap or overlap. If all 16,638 rows are supplied, it also generates the equality for the full score. The current compiled assembly covers the first 144. [144-row theorem](DottieFastReferencePrefix144.lean#L59) · [Axioms](DottieFastReferencePrefix144.audit.txt) · [Span assembler](assemble_fast_reference_spans.py)

To replay a generated assembly, compile each imported span to an object on the Lean module path before compiling the assembly. From this packet directory, an example assembly command is `python assemble_fast_reference_spans.py generated DottieFastReferenceRows80To96.lean DottieFastReferenceRows96To112.lean`.

## Check the Gaussian signs once

The signs depend on the lattice pair, so the same sign certificate works for every integer weight. Lean checked the archived reference subtotal over 1,024 pairs in row 11763 using those signs. It also checked both coordinates of all eleven original sharp moments over 32 pairs in row 26858 using one sign certificate. These are zero-based row indices. To replay the applications, build `DottieCertifiedPairSigns`, `DottieCertifiedPairSignExamples`, and the original `DottieSharpMomentBlock` to objects on the module path, then check `DottieCertifiedPairSignApplications`. [Weight-independent theorem](DottieCertifiedPairSigns.lean#L66) · [Applications](DottieCertifiedPairSignApplications.lean#L12) · [Axioms](DottieCertifiedPairSignApplications.audit.txt)

## Compute both coordinates of all eleven moments together

The joint evaluation preserves the midpoint ticks in the original scalar weights. It reuses the inverse square root, log interval, and phase at each norm, then advances the degree. On the same 32 pairs in row 26858, the joint check took 13.156 seconds and the separate scalar checks took 39.887 seconds on one worker with the same imports. [Joint reduction](DottieJointMomentScore.lean) · [Joint audit](DottieJointSharpBlock.audit.txt) · [Scalar audit](DottieSharpBlockScalarReplay.audit.txt)

The first 1,024 pairs of that row also passed for all eleven complex moments. The single evaluation reached the local memory limit. Eight files with 128 pairs each replayed within it, and Lean assembled the exact 22 integer totals. Build the eight `DottieJointSharpChunk*.lean` files to objects on the module path before replaying the assembly. [1,024-pair theorem](DottieJointSharp1024Assembly.lean#L30) · [Axioms](DottieJointSharp1024Assembly.audit.txt)

The circle theorem accepts the full eleven complex totals, the eleven box comparisons, and the reference ceiling of `0.171687`. It uses the existing uniform rounding proof. The reference replay now joins the first 176 consecutive rows. [Circle theorem](DottieJointSharpCircle.lean#L17) · [176-row reference audit](DottieFastReferencePrefix176.audit.txt)

## Assemble complete sharp rows

Lean verifies the axis and any diagonal together with all off-diagonal pairs. It also adds adjacent ranges of complete rows at the same cutoff. All eleven complex moments are checked on rows 100 and 101 and on their combined span. The last row, 37983, combines blocks of 128 and 109 off-diagonal pairs with its axis. The diagonal is outside the cutoff there. Build `DottieJointMomentRows` and the four `DottieJointRowBody*.lean` files to objects on the module path, then replay `DottieFullSharpRows`. The reference subtotal now covers the first 208 consecutive rows. [Row and span rules](DottieJointMomentRows.lean#L74) · [Complete rows](DottieFullSharpRows.lean#L127) · [Axioms](DottieFullSharpRows.audit.txt) · [Reference subtotal](DottieFastReferencePrefix208.lean#L95)

## Exact integer ranges for the sharp box checks

If a target component has endpoints `L` and `U`, its admissible score ticks run from `ceil(L/32^k) + 1475739525897` through `floor(U/32^k) - 1475739525897`, inclusive. The padding is the original `8/10^8` rounded out in the normalized integer units. Lean verified the endpoints for all 22 ranges. If the full real and imaginary sums lie within those ranges and the reference is at most `0.171687`, the original circle inequality follows. A certified enclosure contained in an admissible range supplies the corresponding sum bound. [Exact equivalence](DottieSharpScoreRanges.lean#L72) · [Endpoint table](DottieSharpScoreRangeTable.lean#L8) · [Circle theorem](DottieSharpScoreRanges.lean#L90)

## Cache the phase and Taylor coefficients

Lean proves that the integer phase reduction gives the original interval endpoints at every norm. The Taylor calculation uses the two nonzero products on the imaginary axis and reuses the checked coefficient endpoints. The midpoint weights and complete block totals agree exactly with the original calculation. Build `DottieFastSharpTaylor` before `DottieFastSharpWeights`. [Taylor identity](DottieFastSharpTaylor.lean#L83) · [Exact block identity](DottieFastSharpWeights.lean#L165)

With the same 1,024 pairs, signs, imports, and one-worker setup, the rational replay took 73.433 seconds and the cached replay took 58.734 seconds. Both runs used eight separate 128-pair checks in one Lean process. The single 1,024-pair computation reached the memory limit. [Rational replay audit](DottieSharpRational1024Chunks.audit.txt) · [Cached replay audit](DottieSharpCached1024Chunks.audit.txt)

The reference subtotal now covers the first 256 consecutive rows. [Reference theorem](DottieFastReferencePrefix256.lean#L122) · [Axioms](DottieFastReferencePrefix256.audit.txt)

## Direct row replay for the full sharp prefix

The direct evaluator uses the same lattice signs and sums both coordinates of all eleven moments. Lean proves that every full row and every contiguous span agrees with the original scalar sums. The exact table for rows 100 and 101 passes again using this evaluator. [Row identities](DottieDirectJointMomentRows.lean) · [Span and circle theorems](DottieDirectJointMomentSpans.lean#L29) · [Two-row proof](DottieDirectJointMomentSpanExample.lean#L11) · [Axiom audit](DottieDirectJointMomentSpanExample.audit.txt)

Use the pinned Lean and compiled imports to run the ranges in the [run plan](DottieSharpCandidateRunPlan.json). For each range, pass its start, stop and output path to `replay_sharp_candidates.py` along with the Lean executable and `DottieSharpCandidateMain.lean`. Keep the plan and its checkpoint files in one directory. The runner saves completed rows and resumes at the first unfinished row.

Run `python -B collect_sharp_candidates.py <plan>` to see progress. With all 37,984 rows present, `--lean-output DottieFullSharpCandidate.lean` adds the integer totals and their box comparison. Lean checks the boxes with `decide +kernel`. The circle theorem takes the exact equality to the full span and the reference ceiling as explicit inputs.

The compiled run matched all 22 entries on each of the three already certified rows, 100, 101 and 37983. Resuming an interrupted two-row run reproduced the same checkpoint bytes.

## Direct reference score through row 287

The kernel checked the next two ranges, rows 256–271 and 272–287, against the saved candidate totals. The sum through row 287 uses the original weight. Build the two range files before the prefix assembly. [First range](DottieFastReferenceRows256To272.audit.txt) · [Second range](DottieFastReferenceRows272To288.audit.txt) · [288-row theorem](DottieFastReferencePrefix288.lean#L7) · [Axioms](DottieFastReferencePrefix288.audit.txt)

The nine cosine divisors can be reused at each norm. Lean checks their values and proves the cached weight equals the previous exact weight, including its rounding. Both evaluations give the same totals on four 128-pair blocks of row 11763. [Weight identity](DottieCachedReferenceCosine.lean#L51) · [512-pair check](DottieCachedReferenceCosineBench512.lean) · [Audit](DottieCachedReferenceCosineBench512.audit.txt)

## Direct reference score through row 319

Lean checks rows 288–303, 304–311, and 312–319, and adds them to the certified prefix. The final theorem uses the original weight on the first 320 rows. Build the last two range files before their span and build that span and rows 288–303 before the prefix. [Span theorem](DottieFastReferenceSpan304To320.lean) · [320-row theorem](DottieFastReferencePrefix320.lean#L7) · [Axioms](DottieFastReferencePrefix320.audit.txt)
