import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_28_checked :
    Height29GaussIntegerCheck height29GaussTrace true 28 ∧
      Height29GaussIntegerCheck height29GaussTrace false 28 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_29_checked :
    Height29GaussIntegerCheck height29GaussTrace true 29 ∧
      Height29GaussIntegerCheck height29GaussTrace false 29 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_30_checked :
    Height29GaussIntegerCheck height29GaussTrace true 30 ∧
      Height29GaussIntegerCheck height29GaussTrace false 30 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_31_checked :
    Height29GaussIntegerCheck height29GaussTrace true 31 ∧
      Height29GaussIntegerCheck height29GaussTrace false 31 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_07 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 7 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 7 + j.val) := by
  fin_cases j
  · exact coefficient_28_checked
  · exact coefficient_29_checked
  · exact coefficient_30_checked
  · exact coefficient_31_checked

#print axioms height29_gauss_integer_coefficient_block_07

end FieldTarget
