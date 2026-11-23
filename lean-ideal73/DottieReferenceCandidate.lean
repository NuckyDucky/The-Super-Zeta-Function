import DottiePairedRows

/-! Check the strict integer threshold for the complete candidate checkpoint.
The equality between the candidate and the Lean row-span sum is the
remaining certificate input. -/

namespace QuarticModel

def dottiePairedCandidateTicks : ℤ :=
  303339834966217300615369504615526421285720775755844666418981971508403960

theorem dottie_paired_candidate_clears_reference_threshold :
    7*(fixedCosScale : ℤ)^5 < 50*dottiePairedCandidateTicks := by
  decide +kernel

theorem dottieCircleReference_pos_of_candidate_equality
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 =
      dottiePairedCandidateTicks) : 0 < dottieCircleReference := by
  apply dottieCircleReference_pos_of_quick_score
  rw [dottieQuickReferenceScore_eq_row_span, hscore]
  exact dottie_paired_candidate_clears_reference_threshold

#print axioms dottie_paired_candidate_clears_reference_threshold
#print axioms dottieCircleReference_pos_of_candidate_equality

end QuarticModel
