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
- [Transitive axiom audit](transitive-audit.txt) checked 107 named declarations in the package audit.

The numerical signed bounds appear as explicit hypotheses of the two ring implications. The clean transcripts capture the original module-by-module runs. The packaged sources preserve the Lean declarations and place the five adapted Murphy files alongside a copy of their upstream license and notice.
