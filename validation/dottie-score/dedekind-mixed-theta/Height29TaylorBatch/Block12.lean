import DedekindDiscriminant23Height29TaylorData

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
theorem height29_taylor_comparisons_block_12 :
    ∀ j : Fin 8, Height29TaylorComparison (96 + j.val) := by
  decide +kernel

#print axioms height29_taylor_comparisons_block_12

end FieldTarget
