import Height29IntegerTrace.Coefficients00
import Height29IntegerTrace.Coefficients01
import Height29IntegerTrace.Coefficients02
import Height29IntegerTrace.Coefficients03
import Height29IntegerTrace.Coefficients04
import Height29IntegerTrace.Coefficients05
import Height29IntegerTrace.Coefficients06
import Height29IntegerTrace.Coefficients07
import Height29IntegerTrace.Coefficients08

namespace FieldTarget

theorem height29_gauss_integer_coefficients_checked (total : Bool) (k : ℕ) (hk : k < 36) :
    Height29GaussIntegerCheck height29GaussTrace total k := by
  have h (g : Fin 9) (s : Fin 4) :
      Height29GaussIntegerCheck height29GaussTrace true (4 * g.val + s.val) ∧
        Height29GaussIntegerCheck height29GaussTrace false (4 * g.val + s.val) := by
    fin_cases g
    · exact height29_gauss_integer_coefficient_block_00 s
    · exact height29_gauss_integer_coefficient_block_01 s
    · exact height29_gauss_integer_coefficient_block_02 s
    · exact height29_gauss_integer_coefficient_block_03 s
    · exact height29_gauss_integer_coefficient_block_04 s
    · exact height29_gauss_integer_coefficient_block_05 s
    · exact height29_gauss_integer_coefficient_block_06 s
    · exact height29_gauss_integer_coefficient_block_07 s
    · exact height29_gauss_integer_coefficient_block_08 s
  let g : Fin 9 := ⟨k / 4, by omega⟩
  let s : Fin 4 := ⟨k % 4, by omega⟩
  have heq : 4 * g.val + s.val = k := by dsimp only [g, s]; omega
  have hFinal := h g s
  rw [heq] at hFinal
  cases total
  · exact hFinal.2
  · exact hFinal.1

#print axioms height29_gauss_integer_coefficients_checked

end FieldTarget
