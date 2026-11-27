import DottieNormalizedMomentScore

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def referenceBlockMomentTicks : List (ℤ × ℤ) := [
  (-43481151690513308, 24374937816273338),
  (25471317956342990, -14278849261708921),
  (-7460566397293520, 4182278079553700),
  (1456803323226761, -816660111010153),
  (-213349343356466, 119599962788836),
  (24996067257726, -14012342129880)
]

/-- All 6 reference moments in the first 128 off-diagonal pairs of the archived row. -/
theorem referenceBlockMomentTicks_eq (k : Fin 6) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 11763 0 128 =
      (referenceBlockMomentTicks.getD k (0, 0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 11763 0 128 =
      (referenceBlockMomentTicks.getD k (0, 0)).2 := by
  fin_cases k <;> constructor <;> decide +kernel

theorem referenceBlock_within_cutoff : 128 ≤ dottiePairRowSize 276824064 11763 := by
  decide +kernel

#print axioms referenceBlockMomentTicks_eq
#print axioms referenceBlock_within_cutoff

end QuarticModel.DottieFixedIntervals
