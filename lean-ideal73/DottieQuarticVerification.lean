import ArchivedGaussianHalfMellin
import ArchivedQuarticCertificates
import ArchivedDottieSmoothedIdentity
import DottieReferenceMoment
import DottieSignedMoments
import ArchivedQuarticSpectralAddress
import DottieRationalProjection
import DottieNormLog
import DottieReferenceScore
import DottieRowSign
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
    `QuarticModel.dottieCircleReference_eq_phase_projection,
    `QuarticModel.signed_dirichlet_taylor_bound,
    `QuarticModel.dottieReferencePolynomial_eq_scaled_dirichlet,
    `QuarticModel.dottie_reference_taylor_bound,
    `QuarticModel.archivedMomentMass_le_cutoff,
    `QuarticModel.dottie_reference_taylor_absolute_error,
    `QuarticModel.archivedDottieAddresses_separate,
    `QuarticModel.archivedFieldZero_at_chart,
    `QuarticModel.archivedDottie_chart_painted_orders,
    `QuarticModel.archivedMomentMass_le_two_sqrt,
    `QuarticModel.dottie_unit_phase_distance,
    `QuarticModel.signed_dirichlet_height_bound,
    `QuarticModel.dottie_reference_rational_height_error,
    `QuarticModel.dottie_reference_rational_norm_bound,
    `QuarticModel.dottieCircleReference_eq_completed_phase,
    `QuarticModel.dottieCircleReference_pos_of_moments,
    `QuarticModel.dottieCircleReference_pos_of_rational_projection,
    `QuarticModel.logAtanhLowerTicks_spec,
    `QuarticModel.normLogBounds_spec,
    `QuarticModel.normLogBounds_width,
    `QuarticModel.dottieNormAngleQuarter_abs_le,
    `QuarticModel.dottie_norm_angle_reduction,
    `QuarticModel.fixedCosBounds_spec,
    `QuarticModel.fixedCosBounds_width,
    `QuarticModel.inverseSqrtTicks_spec,
    `QuarticModel.dottieCosineTicks_spec,
    `QuarticModel.dottieRationalReferenceProjection_eq_sum,
    `QuarticModel.dottieReferenceScoreRows_eq,
    `QuarticModel.dottie_reference_score_error,
    `QuarticModel.dottieCircleReference_pos_of_score,
    `QuarticModel.dottieCircleReference_pos_of_row_score,
    `QuarticModel.dottieTriangleScore_eq_archivedLatticeCoeff,
    `QuarticModel.dottieRowSign_eq_archivedGaussianSign]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing theorem: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError "{name} depends on {axiomName}"
  logInfo m!"Checked the transitive axioms of {targets.size} quartic and Dottie theorems."
