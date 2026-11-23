import DottieNormalizedMomentScore

namespace QuarticModel.DottieFixedIntervals

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

theorem momentOuterRow_1442840576_zero :
    dottiePairedRowSpan 1442840576 (fun n => momentWeightRealTicks n 0) 37983 1 = -5573094568169628 ∧
    dottiePairedRowSpan 1442840576 (fun n => momentWeightImagTicks n 0) 37983 1 = 1918816488819242 := by
  constructor <;> decide +kernel

#print axioms momentOuterRow_1442840576_zero

end QuarticModel.DottieFixedIntervals