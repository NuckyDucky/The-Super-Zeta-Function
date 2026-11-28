import Mathlib.Tactic.FinCases
import Height29TaylorBatch.Block00
import Height29TaylorBatch.Block01
import Height29TaylorBatch.Block02
import Height29TaylorBatch.Block03
import Height29TaylorBatch.Block04
import Height29TaylorBatch.Block05
import Height29TaylorBatch.Block06
import Height29TaylorBatch.Block07
import Height29TaylorBatch.Block08
import Height29TaylorBatch.Block09
import Height29TaylorBatch.Block10
import Height29TaylorBatch.Block11
import Height29TaylorBatch.Block12
import Height29TaylorBatch.Block13
import Height29TaylorBatch.Block14
import Height29TaylorBatch.Block15

namespace FieldTarget

private theorem height29TaylorComparisonsBlock (a : Fin 16) (b : Fin 8) :
    Height29TaylorComparison (a.val * 8 + b.val) := by
  fin_cases a
  · exact height29_taylor_comparisons_block_00 b
  · exact height29_taylor_comparisons_block_01 b
  · exact height29_taylor_comparisons_block_02 b
  · exact height29_taylor_comparisons_block_03 b
  · exact height29_taylor_comparisons_block_04 b
  · exact height29_taylor_comparisons_block_05 b
  · exact height29_taylor_comparisons_block_06 b
  · exact height29_taylor_comparisons_block_07 b
  · exact height29_taylor_comparisons_block_08 b
  · exact height29_taylor_comparisons_block_09 b
  · exact height29_taylor_comparisons_block_10 b
  · exact height29_taylor_comparisons_block_11 b
  · exact height29_taylor_comparisons_block_12 b
  · exact height29_taylor_comparisons_block_13 b
  · exact height29_taylor_comparisons_block_14 b
  · exact height29_taylor_comparisons_block_15 b

theorem height29TaylorComparisons (j : Fin 128) : Height29TaylorComparison j := by
  let a : Fin 16 := ⟨j.val / 8, by omega⟩
  let b : Fin 8 := ⟨j.val % 8, by omega⟩
  have hEq : a.val * 8 + b.val = j.val := by dsimp [a, b]; omega
  rw [← hEq]
  exact height29TaylorComparisonsBlock a b

#print axioms height29TaylorComparisons

end FieldTarget
