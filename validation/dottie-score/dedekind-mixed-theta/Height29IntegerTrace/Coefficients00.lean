import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_0_checked :
    Height29GaussIntegerCheck height29GaussTrace true 0 ∧
      Height29GaussIntegerCheck height29GaussTrace false 0 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_1_checked :
    Height29GaussIntegerCheck height29GaussTrace true 1 ∧
      Height29GaussIntegerCheck height29GaussTrace false 1 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_2_checked :
    Height29GaussIntegerCheck height29GaussTrace true 2 ∧
      Height29GaussIntegerCheck height29GaussTrace false 2 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_3_checked :
    Height29GaussIntegerCheck height29GaussTrace true 3 ∧
      Height29GaussIntegerCheck height29GaussTrace false 3 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_00 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 0 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 0 + j.val) := by
  fin_cases j
  · exact coefficient_0_checked
  · exact coefficient_1_checked
  · exact coefficient_2_checked
  · exact coefficient_3_checked

#print axioms height29_gauss_integer_coefficient_block_00

end FieldTarget
