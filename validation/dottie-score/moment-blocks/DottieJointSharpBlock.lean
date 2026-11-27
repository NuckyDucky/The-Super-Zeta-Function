import DottieCertifiedPairSignExamples
import DottieJointMomentScore
import DottieSharpMomentBlock

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 18000000

/-- The original eleven complex subtotals, computed together in one check. -/
theorem dottie_joint_sharp_block_ticks :
    dottieJointMomentBlock 11 26858 0 32 sharpPairSigns26858 = sharpBlockMomentTicks := by
  decide +kernel

theorem dottie_joint_sharp_block_eq (k : Fin 11) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0,0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0,0)).2 := by
  have h := dottie_joint_moment_block_getD 26858 0 32 sharpPairSigns26858 k.isLt
  rw [dottie_joint_sharp_block_ticks] at h
  constructor
  · rw [sharpPairSigns26858_eq]
    exact (congrArg Prod.fst h).symm
  · rw [sharpPairSigns26858_eq]
    exact (congrArg Prod.snd h).symm

#print axioms dottie_joint_sharp_block_ticks
#print axioms dottie_joint_sharp_block_eq

end QuarticModel.DottieFixedIntervals
