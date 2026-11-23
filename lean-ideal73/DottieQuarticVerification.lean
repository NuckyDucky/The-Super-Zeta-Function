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
import DottieFirstReferenceBlock
import DottieQuickScore
import DottieSymmetricChunks
import DottieFirstPairedRows
import ArchivedDottieRangeIntegral
import ArchivedDottieOmittedBudget
import DottieSharpCircleMoments
import DottieGammaRatio
import ArchivedQuarticSignedPatchCover
import DottieSignedBlockVariation
import DottieDyadicNormBlocks
import DottieReferenceCandidate
import DottiePairedRow11000
import DottieStructuralPairBlocks
import DottieOmittedHorizontalSlope
import DottieWitnessPairBlocks
import DottieSharpBlockDerivative
import DottieJointOmittedDerivative
import DottieRightContourShift
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
    `QuarticModel.dottieRowSign_eq_archivedGaussianSign,
    `QuarticModel.dottieAngleTicks_eq_quarter,
    `QuarticModel.dottieAngleDenominator_pos,
    `QuarticModel.dottieAngleNumerator_natAbs_le,
    `QuarticModel.fixedCosBounds_eq_of_div_eq,
    `QuarticModel.dottieAngleTicks_fixedCosBounds,
    `QuarticModel.dottieRowChunk_eq_sum,
    `QuarticModel.dottieRowChunk_add,
    `QuarticModel.dottieRowChunk_eq_blocks,
    `QuarticModel.dottieReferenceScoreRows_eq_chunks,
    `QuarticModel.dottieReferenceScoreRows_eq_block_sums,
    `QuarticModel.dottieFirstReferenceBlock,
    `QuarticModel.dottieNormAngleQuarterOf_abs_le,
    `QuarticModel.dottie_norm_angle_reduction_of,
    `QuarticModel.dottie_norm_angle_cosine_error_of,
    `QuarticModel.dottieAngleTicks_eq_quarter_of,
    `QuarticModel.dottieAngleNumeratorOf_natAbs_le,
    `QuarticModel.dottieQuickLogLowerTicks_spec,
    `QuarticModel.dottieLogMantissaTicks_eq,
    `QuarticModel.dottieCachedLogLowerTicks_eq,
    `QuarticModel.dottieCachedLogLowerTicks_spec,
    `QuarticModel.dottie_generic_score_error,
    `QuarticModel.dottieCircleReference_pos_of_generic_score,
    `QuarticModel.dottieQuickWeightTicks_spec,
    `QuarticModel.dottie_quick_reference_score_error,
    `QuarticModel.dottieCircleReference_pos_of_quick_score,
    `QuarticModel.dottieTriangleScore_eq_reference_blocks,
    `QuarticModel.dottieSymmetricScore_eq_dottieTriangleScore,
    `QuarticModel.dottiePairRowBlock_add,
    `QuarticModel.dottiePairRowBlock_eq_blocks,
    `QuarticModel.dottieSymmetricScore_eq_blocks,
    `QuarticModel.dottieQuickReferenceScore_eq_symmetric,
    `QuarticModel.dottieCircleReference_pos_of_symmetric_score,
    `QuarticModel.dottiePairedRowSpan_add,
    `QuarticModel.dottiePairedRowSpan_one,
    `QuarticModel.dottieSymmetricScore_eq_row_span,
    `QuarticModel.dottieQuickReferenceScore_eq_row_span,
    `QuarticModel.dottieFirstPairedRows,
    `QuarticModel.dottie_omitted_norm_iff,
    `QuarticModel.dottie_omitted_eq_finite_sum,
    `QuarticModel.dottie_retained_eq_finite_add_far_tail,
    `QuarticModel.dottie_full_sum_finite_partition,
    `QuarticModel.dottie_range_integrand_integrable,
    `QuarticModel.dottie_range_side_eq_sum,
    `QuarticModel.dottie_omitted_eq_range_integrals,
    `QuarticModel.dottieRetained_eq_smoothedPrefix_add_beyond,
    `QuarticModel.archivedDottie_model_margin_of_uniform_error,
    `QuarticModel.dottieRetained_model_of_sharp_budget,
    `QuarticModel.dottieRetained_model_of_split_budget,
    `QuarticModel.dottieOmitted_eq_sharp_add_middle_add_errors,
    `QuarticModel.dottieOmitted_tail_of_split_budget,
    `QuarticModel.dottie_sharp_prefix_eq_completed_dirichlet,
    `QuarticModel.dottie_sharp_circle_offset,
    `QuarticModel.dottie_sharp_moments_error,
    `QuarticModel.dottie_sharp_circle_completed_moments_error,
    `QuarticModel.dottie_gamma_ratio_with_error,
    `StripCover.boxMargins_of_signedPatchBounds,
    `StripCover.hasSignedPatchBounds_of_axisBounds,
    `QuarticModel.archivedGaussian_strip_of_signedPatchBounds,
    `QuarticModel.archivedQuarticRH_of_signedPatchBounds,
    `QuarticModel.dottie_signed_block_variation,
    `QuarticModel.dottie_signed_block_lipschitz,
    `QuarticModel.dottie_signed_block_exp_displacement,
    `QuarticModel.dottie_signed_block_log_weight,
    `QuarticModel.dottie_norm_block_eq_Ioc,
    `QuarticModel.dottie_omitted_sharp_eq_norm_block,
    `QuarticModel.dottie_norm_block_shift_error,
    `QuarticModel.dottie_norm_block_completed_shift_error,
    `QuarticModel.dottie_omitted_sharp_circle_anchored_error,
    `QuarticModel.archivedLatticeCoeff_two_mul,
    `QuarticModel.dottie_norm_block_eq_prefix_sub,
    `QuarticModel.dottie_even_norm_weighted,
    `QuarticModel.dottie_norm_block_dyadic,
    `QuarticModel.dottie_first_omitted_dyadic,
    `QuarticModel.dottie_paired_candidate_clears_reference_threshold,
    `QuarticModel.dottieCircleReference_pos_of_candidate_equality,
    `QuarticModel.dottiePairedRow11000,
    `QuarticModel.dottieStructuralRowSign_eq,
    `QuarticModel.dottieLookupRowSign_eq,
    `QuarticModel.dottie_pair_row_block_with_sign_eq,
    `QuarticModel.dottie_joint_omitted_eq_two_sides,
    `QuarticModel.dottie_joint_omitted_im_le_of_horizontal_slope,
    `QuarticModel.dottie_joint_ring_budget_of_horizontal_slope,
    `QuarticModel.dottie_large_sign_of_witness,
    `QuarticModel.dottie_pair_block_of_witness,
    `QuarticModel.dottie_pair_block_of_packed_witness,
    `QuarticModel.dottie_norm_block_hasDerivAt,
    `QuarticModel.dottie_completed_norm_block_hasDerivAt,
    `QuarticModel.dottie_centered_log_block_bound,
    `QuarticModel.dottie_completed_derivative_anchor_error,
    `QuarticModel.dottie_range_integrand_hasDerivAt,
    `QuarticModel.dottie_range_integrand_differentiableAt,
    `QuarticModel.dottie_range_integrand_continuous,
    `QuarticModel.dottie_range_integrand_deriv_continuous,
    `QuarticModel.dottie_range_contour_uniform_value_bound,
    `QuarticModel.dottie_range_contour_derivative_bound,
    `QuarticModel.dottie_range_side_hasDerivAt,
    `QuarticModel.dottie_joint_omitted_hasDerivAt,
    `QuarticModel.dottie_omitted_horizontal_hasDerivAt,
    `QuarticModel.dottie_joint_ring_budget_of_signed_derivative,
    `QuarticModel.dottie_right_side_eq_range_side,
    `QuarticModel.dottie_right_side_hasDerivAt,
    `QuarticModel.dottie_omitted_far_eq_right_contours,
    `QuarticModel.archived_coeff_prefix_abs_le_linear]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing theorem: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError "{name} depends on {axiomName}"
  logInfo m!"Checked the transitive axioms of {targets.size} quartic and Dottie theorems."
