import Height29IntegerTrace.Table
import Discriminant23GaussIntegerComparison

namespace FieldTarget

set_option exponentiation.threshold 1024

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_24_checked :
    Height29GaussIntegerCheck height29GaussTrace true 24 ∧
      Height29GaussIntegerCheck height29GaussTrace false 24 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_25_checked :
    Height29GaussIntegerCheck height29GaussTrace true 25 ∧
      Height29GaussIntegerCheck height29GaussTrace false 25 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_26_checked :
    Height29GaussIntegerCheck height29GaussTrace true 26 ∧
      Height29GaussIntegerCheck height29GaussTrace false 26 := by
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_27_checked :
    Height29GaussIntegerCheck height29GaussTrace true 27 ∧
      Height29GaussIntegerCheck height29GaussTrace false 27 := by
  constructor
  · decide +kernel
  · decide +kernel

theorem height29_gauss_integer_coefficient_block_06 (j : Fin 4) :
    Height29GaussIntegerCheck height29GaussTrace true (4 * 6 + j.val) ∧
      Height29GaussIntegerCheck height29GaussTrace false (4 * 6 + j.val) := by
  fin_cases j
  · exact coefficient_24_checked
  · exact coefficient_25_checked
  · exact coefficient_26_checked
  · exact coefficient_27_checked

#print axioms height29_gauss_integer_coefficient_block_06

end FieldTarget
