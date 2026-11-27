import DottieMomentArchiveScores

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection
set_option autoImplicit false

/-- The sharp-circle checks use the six reference moments through a single
upper bound on the projected reference value. A direct certificate for
that reference value can supply the bound at the same input. -/
theorem dottie_sharp_margin_of_reference_projection
    (hsharp : ∀ k < 11, (archivedScoredMomentBox dottiePrefixEnd k).fits (fixedSharpInput k) = true)
    (href : dottieRelativeReferenceProjection ≤
      (fixedReferenceTicks : ℝ) / (dottieSharpArcScale : ℝ)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048),
      (dottieSharpPrefix w).im ≤ -(190.37 * ((w.re - 1 / 2) * dottieCircleReference)) := by
  apply dottie_sharp_margin_of_factored_arc_bounds fixedCheckedArcs fixedReferenceTicks
    fixedCheckedArcs_cover fixedCheckedArcs_scalar href
  intro a ha t ht
  have hpass := List.all_eq_true.mp fixedCheckedArcs_pass a ha
  rw [fixedReferenceTicks_eq] at hpass
  refine fixedArcPass_sound hpass ?_ ht
  intro k _
  by_cases hk : k < 11
  · exact archivedMomentBox_of_uniform_scores (N := dottiePrefixEnd) le_rfl rfl rfl (hsharp k hk)
  · simpa only [fixedSharpInput, if_neg hk] using sharpTailMomentBox_sound k

#print axioms dottie_sharp_margin_of_reference_projection

end QuarticModel.DottieFixedIntervals
