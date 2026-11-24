import DottieFixedSharpArchive
import DottieUniformMomentWidth
import DottieRetainedBandBounds
import DottieShorterOmittedBudget

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

/-- State the retained side of the same-input contradiction using its
actual score checks and band sums. -/
theorem dottie_right_field_nonzero_of_archive_score_checks
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks)
    (h₄ : DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12)
    (h₂ : DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482)
    (h₁ : DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338)
    (hsharp : ∀ k < 11, (archivedScoredMomentBox dottiePrefixEnd k).fits (fixedSharpInput k) = true)
    (href : ∀ k < 6, (archivedScoredMomentBox 276824064 k).fits (fixedReferenceInput k) = true)
    (hsigned : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmittedSharpBlock z + dottieShorterMiddleSmooth z).im ≤
        188*((z.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink : ℂ → ℂ)
    (hR : riemannZeta w ≠ 0) (hB : FieldCoefficientTransfer.chi4.LFunction w ≠ 0) :
    archivedQuarticZeta w ≠ 0 := by
  apply dottie_right_field_nonzero_of_shorter_signed_block hscore _ hsigned hw ink hR hB
  apply dottie_retained_margin_of_finite_band_bound
    (dottieCircleReference_lower_of_candidate_equality hscore)
    (dottie_sharp_margin_of_archive_score_checks hsharp href)
  intro z hz
  obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hz
  exact dottie_retained_bands_bound_of_integer_sums h₄ h₂ h₁ hr hi

#print axioms dottie_sharp_margin_of_archive_score_checks
#print axioms dottie_right_field_nonzero_of_archive_score_checks

end QuarticModel.DottieFixedIntervals
