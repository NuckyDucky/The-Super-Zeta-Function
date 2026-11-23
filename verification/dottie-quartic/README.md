# Dottie quartic verification

These records use Lean 4.33.1 and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean package](../../lean-ideal73/README.md#the-exact-dottie-quartic-and-the-signed-ring-test) contains the sources and reproduction commands.

- [Quartic and smoothed contour proof](quartic-contour-replay.txt) rebuilt 68 project modules.
- [Gamma phase](reference-phase-replay.txt) rebuilt the five modules involved in the phase enclosure.
- [Reference projection](reference-bridge.txt) assembled the reference proof against those two replays.
- [Signed moments](signed-moments.txt) checked the exact Taylor error and absolute mass bounds.
- [Chart replay](chart-replay.txt) accepted all 43 modules of the original Super Zeta chart on the quartic toolchain.
- [Spectral bridge](spectral-bridge.txt) checked the original address, zero test, and Hamilton order implications.
- [Rational reference](rational-reference.txt) checked the sharper lattice-mass bound, the completed phase, the perturbation to a rational height, the conditional positivity test, and the integer log enclosures.
- [Integer reference score](integer-reference-score.txt) checked the rational phase reduction, Taylor cosine enclosure, integer reciprocal square root, exact signed lattice character, and the implication from the score inequality to positivity.
- [Score block replay](score-block-replay.txt) checked fixed-denominator phase reduction, exact row partition and recombination, and the first 1,024-point block.
- [Cached log evaluator](cached-log-score.txt) checked the lookup and eight-term residual, the per-weight error, and the original positivity implication.
- [First complete reference row](first-reference-row.txt) checked all 17 blocks and their exact sum.
- [Paired Gaussian score](paired-reference-score.txt) checked the swapped-coordinate sum, its batch decomposition, and its positivity implication.
- [Paired row spans](paired-row-span.txt) checked contiguous span assembly and the exact sum of the first 32 paired rows.
- [Signed Dottie budgets](signed-dottie-budgets.txt) audited the exact signed norm partition, range contour identity, retained and omitted margin implications, uniform sharp moments, Gamma ratio, and signed patch transfer.
- [Signed block variation](signed-block-variation.txt) checked both Gaussian signed partial-summation transfer estimates for complex displacement and the log-weighted derivative.
- [Omitted sharp block and reference candidate](omitted-sharp-and-candidate.txt) checked the exact block, the whole-circle anchor error, even norm reuse, the candidate integer margin, and row 11,000 of the actual certificate.
- [Candidate checkpoint receipt](full-paired-checkpoint-receipt.json) records the ordered coverage, SHA-256, and integer total for all 16,638 rows. The equality of the complete candidate to the Lean row-span sum remains an explicit input.
- [Lookup and horizontal slope](lookup-and-horizontal-slope.txt) checked the exact sign equivalences, the original block score, and the derivative implication for the exact Dottie ring.
- [Paired sign timings](paired-sign-timing.txt) record a same-process 256-position profile and the replay of row 11,000 using the original and lookup evaluators.
- [Packed witnesses and sharp derivative](packed-witness-and-sharp-derivative.txt) checked modular sign witnesses, exact packed block certification and the derivative estimate for the original sharp block.
- [Packed witness timings](packed-witness-timing.txt) record the same 256 positions, the rejection of a corrupted root, and the full row 11,000 replay.
- [Horizontal derivative](horizontal-derivative.txt) checks the pointwise contour derivative, a uniform integrable majorant, differentiation under the integral, and the exact signed-derivative implication for the ring.
- [Far contour shift](far-contour-shift.txt) checks the exact shifted expression for the far omitted block and proves a linear unsigned Gaussian coefficient count.
- [Absolute far bound](far-absolute-bound.txt) checks the weighted Gaussian coefficient count, the central and outer Gamma bounds, the scalar norm bound, and the lower bound for the reference Gamma ratio.
- [Lower smoothing and reference](lower-smoothing-budgets.txt) checks the exact rectangle, its four edge bounds, the prefix and lower omitted smoothing budgets, and the relative far budget from the exact row equality.
- [Retained band and tail split](retained-band-tail-budget.txt) checks the exact finite bands, the absolute infinite-tail bound, and the revised sufficient finite-band budget.
- [Signed finite-band variation](retained-band-variation.txt) checks the Abel bound, one-step bound for the original contour polynomial, and exact phase-length constants for its three intervals.
- [Integrated retained bands](retained-band-integration.txt) checks the original core and tail integrals, the conditional ring assembly, the coefficient zero checker, and the first eight actual zero coefficients.
- [First checked band chunk](retained-band-first-chunk.txt) checks the Lucas witness, the split prime-power formula and the actual 16-slot integer sum certificate.
- [Retained band batch replay](retained-band-chunk-replay.txt) checks the generic factor and prefix replay, the first 32 and 256 norms, and all 4,096 norms of the first archived short band. The single-worker short-band build took 44.003 seconds and peaked at 6,826.5 MiB of sampled private memory.
- [All short bands and the relative circle](retained-short-bands-relative-circle.txt) gives the remaining short-band certificates and the exact relative Gamma and sharp-circle transport. The second and third short bands took 40.702 and 45.412 seconds on one worker.
- [Transitive axiom audit](transitive-audit.txt) checked 249 named declarations in the package audit.

The numerical signed bounds appear as explicit hypotheses of the two ring implications. The clean transcripts capture the original module-by-module runs. The packaged sources preserve the Lean declarations and place the five adapted Murphy files alongside a copy of their upstream license and notice.
