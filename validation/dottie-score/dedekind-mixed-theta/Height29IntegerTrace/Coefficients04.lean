import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_16_checked :
    Height29GaussIntegerCheck height29GaussTrace true 16 ∧
      Height29GaussIntegerCheck height29GaussTrace false 16 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_17_checked :
    Height29GaussIntegerCheck height29GaussTrace true 17 ∧
      Height29GaussIntegerCheck height29GaussTrace false 17 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_18_checked :
    Height29GaussIntegerCheck height29GaussTrace true 18 ∧
      Height29GaussIntegerCheck height29GaussTrace false 18 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_19_checked :
    Height29GaussIntegerCheck height29GaussTrace true 19 ∧
      Height29GaussIntegerCheck height29GaussTrace false 19 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_04 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 4 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 4 + j.val) := by
  fin_cases j
  · exact coefficient_16_checked
  · exact coefficient_17_checked
  · exact coefficient_18_checked
  · exact coefficient_19_checked

#print axioms height29_gauss_integer_coefficient_block_04

end FieldTarget
