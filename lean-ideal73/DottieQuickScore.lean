import DottieGenericScore
import DottieQuickWeights
import DottieScoreChunks

/-! The cached-log evaluator in the exact original quartic positivity test. -/

namespace QuarticModel

/-- The integer score with the cached mantissa evaluator. -/
def dottieQuickReferenceScore : ℤ := dottieTriangleScore 276824064 dottieQuickWeightTicks

theorem dottie_quick_reference_score_error :
    |(dottieQuickReferenceScore : ℝ)/(fixedCosScale : ℝ)^5-dottieRationalReferenceProjection| ≤ 1/25 :=
  dottie_generic_score_error dottieQuickWeightTicks dottieQuickWeightTicks_spec

theorem dottieCircleReference_pos_of_quick_score
    (h : 7*(fixedCosScale:ℤ)^5 < 50*dottieQuickReferenceScore) : 0 < dottieCircleReference :=
  dottieCircleReference_pos_of_generic_score dottieQuickWeightTicks dottieQuickWeightTicks_spec h

#print axioms dottie_quick_reference_score_error
#print axioms dottieCircleReference_pos_of_quick_score

end QuarticModel
