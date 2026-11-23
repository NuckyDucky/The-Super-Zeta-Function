import DottieNormalizedMomentScore

namespace QuarticModel.DottieFixedIntervals

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

theorem momentOuterRow_276824064_zero :
    dottiePairedRowSpan 276824064 (fun n => momentWeightRealTicks n 0) 16637 1 = 8318327505840388 ∧
    dottiePairedRowSpan 276824064 (fun n => momentWeightImagTicks n 0) 16637 1 = 2981087333998190 := by
  constructor <;> decide +kernel

#print axioms momentOuterRow_276824064_zero

end QuarticModel.DottieFixedIntervals