import DottieNormalizedMomentScore

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def sharpBlockMomentTicks : List (ℤ × ℤ) := [
  (-4026942645296952, -3302372327692728),
  (2566762400349065, 2104923089863426),
  (-818023721735913, -670836110314635),
  (173802039288009, 142529700671477),
  (-27695237978454, -22712010349266),
  (3530574024681, 2895314656100),
  (-375063062998, -307577607208),
  (34152026655, 28007017950),
  (-2721051230, -2231449579),
  (192710077, 158035545),
  (-12283289, -10073138)
]

/-- All eleven sharp moments in the first 32 off-diagonal pairs of zero-based row 26858. -/
theorem sharpBlockMomentTicks_eq (k : Fin 11) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0, 0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 26858 0 32 =
      (sharpBlockMomentTicks.getD k (0, 0)).2 := by
  fin_cases k <;> constructor <;> decide +kernel

theorem sharpBlock_within_cutoff : 32 ≤ dottiePairRowSize 1442840576 26858 := by
  decide +kernel

#print axioms sharpBlockMomentTicks_eq
#print axioms sharpBlock_within_cutoff

end QuarticModel.DottieFixedIntervals
