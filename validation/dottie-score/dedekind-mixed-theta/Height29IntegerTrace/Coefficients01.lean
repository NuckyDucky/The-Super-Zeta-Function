import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_4_checked :
    Height29GaussIntegerCheck height29GaussTrace true 4 ∧
      Height29GaussIntegerCheck height29GaussTrace false 4 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_5_checked :
    Height29GaussIntegerCheck height29GaussTrace true 5 ∧
      Height29GaussIntegerCheck height29GaussTrace false 5 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_6_checked :
    Height29GaussIntegerCheck height29GaussTrace true 6 ∧
      Height29GaussIntegerCheck height29GaussTrace false 6 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_7_checked :
    Height29GaussIntegerCheck height29GaussTrace true 7 ∧
      Height29GaussIntegerCheck height29GaussTrace false 7 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_01 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 1 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 1 + j.val) := by
  fin_cases j
  · exact coefficient_4_checked
  · exact coefficient_5_checked
  · exact coefficient_6_checked
  · exact coefficient_7_checked

#print axioms height29_gauss_integer_coefficient_block_01

end FieldTarget
