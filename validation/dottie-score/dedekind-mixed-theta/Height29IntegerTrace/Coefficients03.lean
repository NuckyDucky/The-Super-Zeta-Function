import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_12_checked :
    Height29GaussIntegerCheck height29GaussTrace true 12 ∧
      Height29GaussIntegerCheck height29GaussTrace false 12 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_13_checked :
    Height29GaussIntegerCheck height29GaussTrace true 13 ∧
      Height29GaussIntegerCheck height29GaussTrace false 13 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_14_checked :
    Height29GaussIntegerCheck height29GaussTrace true 14 ∧
      Height29GaussIntegerCheck height29GaussTrace false 14 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_15_checked :
    Height29GaussIntegerCheck height29GaussTrace true 15 ∧
      Height29GaussIntegerCheck height29GaussTrace false 15 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_03 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 3 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 3 + j.val) := by
  fin_cases j
  · exact coefficient_12_checked
  · exact coefficient_13_checked
  · exact coefficient_14_checked
  · exact coefficient_15_checked

#print axioms height29_gauss_integer_coefficient_block_03

end FieldTarget
