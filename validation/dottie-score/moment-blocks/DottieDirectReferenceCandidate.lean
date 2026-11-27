import DottieDirectReferenceScore

namespace QuarticModel

/-- Integer produced by the recorded four-part calculation of the reference rows. -/
def dottieDirectReferenceCandidateScore : ℤ :=
  19879640713048077117805831446842812936838570470903723675275356591893472361144

/-- The comparison for this integer uses kernel arithmetic. -/
theorem dottie_direct_reference_candidate_passes :
    (10^7 : ℤ) * |dottieDirectReferenceCandidateScore| ≤
      1716866 * (dottieDirectReferenceDenominator : ℤ) := by
  decide +kernel

/-- The full row equality is the remaining input from the arithmetic replay. -/
theorem dottie_reference_decimal_of_candidate_eq
    (hrows : dottieDirectReferenceScore = dottieDirectReferenceCandidateScore) :
    dottieRelativeReferenceProjection ≤ 171687/10^6 := by
  apply dottie_reference_decimal_of_direct_score_bound
  rw [hrows]
  exact dottie_direct_reference_candidate_passes

#print axioms dottie_direct_reference_candidate_passes
#print axioms dottie_reference_decimal_of_candidate_eq

end QuarticModel
