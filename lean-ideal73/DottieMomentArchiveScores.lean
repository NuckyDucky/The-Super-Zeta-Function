import DottieFixedSharpArchive
import DottieUniformMomentWidth

/-! Reduce the seventeen moment hypotheses of the original circle to
exact integer-score comparisons. The analytic rounding allowance is
proved uniformly for the entire archived norm range. -/

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection
set_option autoImplicit false

def archivedScoredMomentBox (N k : ℕ) : Rect :=
  momentScoreRect
    (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) 0 N.sqrt)
    (dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) 0 N.sqrt)
    k (8/10^8)

theorem dottie_sharp_margin_of_archive_score_checks
    (hsharp : ∀ k < 11, (archivedScoredMomentBox dottiePrefixEnd k).fits (fixedSharpInput k) = true)
    (href : ∀ k < 6, (archivedScoredMomentBox 276824064 k).fits (fixedReferenceInput k) = true) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_margin_of_fixed_archive_moments
  · intro k hk
    exact archivedMomentBox_of_uniform_scores (N := dottiePrefixEnd) le_rfl rfl rfl (hsharp k hk)
  · intro k hk
    exact archivedMomentBox_of_uniform_scores (N := 276824064) (by decide +kernel) rfl rfl (href k hk)

#print axioms dottie_sharp_margin_of_archive_score_checks

end QuarticModel.DottieFixedIntervals
