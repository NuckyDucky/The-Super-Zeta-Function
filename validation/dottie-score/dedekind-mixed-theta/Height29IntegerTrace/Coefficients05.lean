import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_20_checked :
    Height29GaussIntegerCheck height29GaussTrace true 20 ∧
      Height29GaussIntegerCheck height29GaussTrace false 20 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_21_checked :
    Height29GaussIntegerCheck height29GaussTrace true 21 ∧
      Height29GaussIntegerCheck height29GaussTrace false 21 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_22_checked :
    Height29GaussIntegerCheck height29GaussTrace true 22 ∧
      Height29GaussIntegerCheck height29GaussTrace false 22 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_23_checked :
    Height29GaussIntegerCheck height29GaussTrace true 23 ∧
      Height29GaussIntegerCheck height29GaussTrace false 23 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_05 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 5 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 5 + j.val) := by
  fin_cases j
  · exact coefficient_20_checked
  · exact coefficient_21_checked
  · exact coefficient_22_checked
  · exact coefficient_23_checked

#print axioms height29_gauss_integer_coefficient_block_05

end FieldTarget
