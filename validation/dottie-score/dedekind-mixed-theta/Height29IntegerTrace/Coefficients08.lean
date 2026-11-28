import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_32_checked :
    Height29GaussIntegerCheck height29GaussTrace true 32 ∧
      Height29GaussIntegerCheck height29GaussTrace false 32 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_33_checked :
    Height29GaussIntegerCheck height29GaussTrace true 33 ∧
      Height29GaussIntegerCheck height29GaussTrace false 33 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_34_checked :
    Height29GaussIntegerCheck height29GaussTrace true 34 ∧
      Height29GaussIntegerCheck height29GaussTrace false 34 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_35_checked :
    Height29GaussIntegerCheck height29GaussTrace true 35 ∧
      Height29GaussIntegerCheck height29GaussTrace false 35 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_08 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 8 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 8 + j.val) := by
  fin_cases j
  · exact coefficient_32_checked
  · exact coefficient_33_checked
  · exact coefficient_34_checked
  · exact coefficient_35_checked

#print axioms height29_gauss_integer_coefficient_block_08

end FieldTarget
