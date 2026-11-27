import DottieCertifiedPairSignExamples
import DottieJointMomentScore
import DottieSharpMomentBlock

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 18000000

theorem dottie_sharp_scalar_replay (k : Fin 11) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0,0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0,0)).2 := by
  constructor
  · rw [sharpPairSigns26858_eq]
    fin_cases k <;> decide +kernel
  · rw [sharpPairSigns26858_eq]
    fin_cases k <;> decide +kernel

#print axioms dottie_sharp_scalar_replay

end QuarticModel.DottieFixedIntervals
