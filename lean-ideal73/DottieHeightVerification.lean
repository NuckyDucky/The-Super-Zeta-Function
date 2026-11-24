import DottieMarkedHeight
import CrossleySignedTail
import DedekindDottieSetup
import Lean.Util.CollectAxioms

/-! Audit the height, marked-return and same-input bound theorems together. -/

open Lean Elab Command in
run_cmd do
  let targets := #[
    `SuperZeta.StirlingCorrection.dottieFlankHeight_inverse,
    `SuperZeta.StirlingCorrection.dottieFlankAtHeight_witness_band,
    `SuperZeta.StirlingCorrection.lifted_arrow_hasDerivAt,
    `SuperZeta.StirlingCorrection.height_from_marked_arrow,
    `SuperZeta.StirlingCorrection.ordered_clock_640,
    `SuperZeta.StirlingCorrection.scalar_period_320_of_divisor_exclusions,
    `SuperZeta.StirlingCorrection.rootedReturn_hasDerivAt,
    `SuperZeta.StirlingCorrection.rootedWinding_of_im_bounds,
    `SuperZeta.StirlingCorrection.dottie_height_covers_witness_band,
    `SuperZeta.StirlingCorrection.dottie_band_selects_marked_returns,
    `SuperZeta.CrossleyQuarter.dyadicShell_div_pow_eq,
    `SuperZeta.CrossleyQuarter.dyadicShell_upper_of_compact_lower,
    `SuperZeta.CrossleyQuarter.riemann_factor_ne_zero_of_ordinary_rh,
    `QuarticModel.archived_right_signed_budget_gap,
    `FieldTarget.readings_ne_of_signed_gap,
    `FieldTarget.dedekindZetaRH_of_same_input_signed_gap]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing theorem {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on {axiomName}"
  logInfo m!"Verified the transitive axioms of all {targets.size} Dottie height and signed-bound theorems."

#check @SuperZeta.StirlingCorrection.dottie_band_selects_marked_returns
#check @SuperZeta.CrossleyQuarter.dyadicShell_upper_of_compact_lower
#check @FieldTarget.dedekindZetaRH_of_same_input_signed_gap
#print axioms SuperZeta.StirlingCorrection.dottie_height_covers_witness_band
#print axioms SuperZeta.StirlingCorrection.dottie_band_selects_marked_returns
#print axioms SuperZeta.CrossleyQuarter.dyadicShell_upper_of_compact_lower
#print axioms FieldTarget.dedekindZetaRH_of_same_input_signed_gap
