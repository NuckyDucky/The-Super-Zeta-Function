import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Extracted unchanged from SuperZeta/FactorialPhase.lean at
7053444979826a20e4393085454a38835602c48f. -/
namespace SuperZeta.StirlingCorrection
open Real
noncomputable section

/-- The exact squared horizontal-to-vertical ratio of the archived witnesses. -/
def witnessRatio : ℝ := (0.00000004749479070945369 / 0.509892982511772)^2

def heightDelta : ℝ := 160 * log (1+witnessRatio)

def dottieHeight : ℝ := 2*π/heightDelta

theorem heightDelta_pos : 0 < heightDelta := by
  have h : 1 < 1+witnessRatio := by norm_num [witnessRatio]
  unfold heightDelta
  exact mul_pos (by norm_num) (log_pos h)

private theorem witness_log_error :
    |log (1+witnessRatio) - (witnessRatio - witnessRatio^2/2)| ≤
      witnessRatio^3 / (1-witnessRatio) := by
  have h₀ : 0 ≤ witnessRatio := by norm_num [witnessRatio]
  have h₁ : |-witnessRatio| < 1 := by norm_num [witnessRatio]
  have h := Real.abs_log_sub_add_sum_range_le h₁ 2
  have hsum : (∑ i ∈ Finset.range 2, (-witnessRatio) ^ (i+1) / (i+1)) =
      -(witnessRatio - witnessRatio^2/2) := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hsum, abs_neg, abs_of_nonneg h₀, sub_neg_eq_add, neg_add_eq_sub] at h
  exact h

/-- A rational enclosure of the original reference height. -/
theorem dottieHeight_enclosure :
    4526119322477.945393315398 < dottieHeight ∧
      dottieHeight < 4526119322477.945393329807 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp witness_log_error
  have hhigh :
      log (1+witnessRatio) ≤
        witnessRatio - witnessRatio^2/2 + witnessRatio^3/(1-witnessRatio) := by linarith
  have hlow :
      witnessRatio - witnessRatio^2/2 - witnessRatio^3/(1-witnessRatio) ≤
        log (1+witnessRatio) := by linarith
  constructor
  · unfold dottieHeight
    apply (lt_div_iff₀ heightDelta_pos).2
    unfold heightDelta
    calc
      _ ≤ 4526119322477.945393315398 * (160 *
          (witnessRatio - witnessRatio^2/2 + witnessRatio^3/(1-witnessRatio))) := by
        gcongr
      _ < 2 * 3.14159265358979323846 := by norm_num [witnessRatio]
      _ < 2 * π := by linarith [Real.pi_gt_d20]
  · unfold dottieHeight
    apply (div_lt_iff₀ heightDelta_pos).2
    unfold heightDelta
    calc
      _ < 2 * 3.14159265358979323847 := by linarith [Real.pi_lt_d20]
      _ < 4526119322477.945393329807 * (160 *
          (witnessRatio - witnessRatio^2/2 - witnessRatio^3/(1-witnessRatio))) := by
        norm_num [witnessRatio]
      _ ≤ _ := by gcongr

#print axioms dottieHeight_enclosure

end
end SuperZeta.StirlingCorrection
