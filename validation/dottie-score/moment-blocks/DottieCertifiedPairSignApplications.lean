import DottieCertifiedPairSignExamples
import DottieFastReferenceScore
import DottieSharpMomentBlock

namespace QuarticModel

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 18000000

/-- The compact signs recover the exact 1024-pair reference subtotal. -/
theorem dottie_reference_block_using_certified_signs :
    dottiePairRowBlock dottieDirectReferenceWeight 11763 0 1024 =
      (414156807032478795629844317576496497541571657112867569451667478094916659312 : ℤ) := by
  rw [← funext dottie_fast_reference_weight_eq, referencePairSigns11763_eq]
  decide +kernel

namespace DottieFixedIntervals

/-- The same proof of the signs serves all eleven complex sharp moments. -/
theorem dottie_sharp_block_using_certified_signs (k : Fin 11) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0, 0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0, 0)).2 := by
  constructor
  · rw [sharpPairSigns26858_eq]
    fin_cases k <;> decide +kernel
  · rw [sharpPairSigns26858_eq]
    fin_cases k <;> decide +kernel

end DottieFixedIntervals

#print axioms dottie_reference_block_using_certified_signs
#print axioms DottieFixedIntervals.dottie_sharp_block_using_certified_signs

end QuarticModel
