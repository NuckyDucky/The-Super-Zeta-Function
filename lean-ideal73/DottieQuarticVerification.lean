import ArchivedGaussianHalfMellin
import ArchivedQuarticCertificates
import ArchivedDottieSmoothedIdentity
import DottieReferenceMoment
import Lean.Util.CollectAxioms

/-! Check the transitive axioms of the exact quartic, the Dottie sum, and its
reference projection, including the implications of the signed ring bounds. -/

open Lean Elab Command in
run_cmd do
  let targets := #[
    `QuarticConductorSign.root_number,
    `QuarticModel.archivedQuarticZeta_isDedekind,
    `QuarticModel.archivedMellin_eq_centered_half,
    `QuarticModel.archivedQuarticRH_iff_boxMargins,
    `SuperZeta.StirlingCorrection.dottieHeight_enclosure,
    `QuarticModel.archivedDottieRing_address,
    `QuarticModel.dottieSmoothTerm_hasSum_normalized,
    `QuarticModel.dottie_normalized_remainder_eq_signed_norm_sum,
    `QuarticModel.dottie_ring_zero_free_of_signed_bounds,
    `QuarticModel.dottie_ring_painted_orders_of_signed_bounds,
    `QuarticModel.dottie_gamma_reference_phase_interval,
    `QuarticModel.dottieCircleReference_eq_phase_projection]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing theorem: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError "{name} depends on {axiomName}"
  logInfo m!"Checked the transitive axioms of {targets.size} quartic and Dottie theorems."
