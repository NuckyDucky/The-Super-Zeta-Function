# Dottie quartic verification

These records use Lean 4.33.1 and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean package](../../lean-ideal73/README.md#the-exact-dottie-quartic-and-the-signed-ring-test) contains the sources and reproduction commands.

- [Quartic and smoothed contour proof](quartic-contour-replay.txt) rebuilt 68 project modules.
- [Gamma phase](reference-phase-replay.txt) rebuilt the five modules involved in the phase enclosure.
- [Reference projection](reference-bridge.txt) assembled the reference proof against those two replays.
- [Signed moments](signed-moments.txt) checked the exact Taylor error and absolute mass bounds.
- [Chart replay](chart-replay.txt) accepted all 43 modules of the original Super Zeta chart on the quartic toolchain.
- [Spectral bridge](spectral-bridge.txt) checked the original address, zero test, and Hamilton order implications.
- [Rational reference](rational-reference.txt) checked the sharper lattice-mass bound, the completed phase, the perturbation to a rational height, the conditional positivity test, and the integer log enclosures.
- [Transitive axiom audit](transitive-audit.txt) checked 31 named declarations in the package audit.

The numerical signed bounds appear as explicit hypotheses of the two ring implications. The clean transcripts capture the original module-by-module runs. The packaged sources preserve the Lean declarations and place the five adapted Murphy files alongside a copy of their upstream license and notice.
