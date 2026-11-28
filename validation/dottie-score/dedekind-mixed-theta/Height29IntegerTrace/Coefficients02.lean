import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_8_checked :
    Height29GaussIntegerCheck height29GaussTrace true 8 ∧
      Height29GaussIntegerCheck height29GaussTrace false 8 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_9_checked :
    Height29GaussIntegerCheck height29GaussTrace true 9 ∧
      Height29GaussIntegerCheck height29GaussTrace false 9 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_10_checked :
    Height29GaussIntegerCheck height29GaussTrace true 10 ∧
      Height29GaussIntegerCheck height29GaussTrace false 10 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_11_checked :
    Height29GaussIntegerCheck height29GaussTrace true 11 ∧
      Height29GaussIntegerCheck height29GaussTrace false 11 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_02 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 2 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 2 + j.val) := by
  fin_cases j
  · exact coefficient_8_checked
  · exact coefficient_9_checked
  · exact coefficient_10_checked
  · exact coefficient_11_checked

#print axioms height29_gauss_integer_coefficient_block_02

end FieldTarget
