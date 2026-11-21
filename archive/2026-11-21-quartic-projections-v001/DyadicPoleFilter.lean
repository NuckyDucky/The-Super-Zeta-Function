import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace DyadicPoleFilter

theorem nonzero_dyadic_multiplier {s : ℂ} (hs : s.re < 1) :
    (2 : ℂ) ^ (1 - s) - 1 ≠ 0 := by
  intro heq
  have hzero := sub_eq_zero.mp heq
  have hn := congrArg norm hzero
  have hnorm := Complex.norm_natCast_cpow_of_pos (n := 2) (by decide) (1 - s)
  norm_num at hnorm hn
  have hp : 1 < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (sub_pos.mpr hs)
  linarith

theorem residue_positive {β m : ℝ} (hβ : 0 < β) (hβ' : β < 1) (hm : 0 < m) :
    0 < m * ((2 : ℝ) ^ (1 - β) - 1) / (β * (1 - β)) := by
  exact div_pos (mul_pos hm (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (sub_pos.mpr hβ'))))
    (mul_pos hβ (sub_pos.mpr hβ'))

theorem linear_centering_cancels (c x : ℝ) : 2 * (c * (x / 2)) - c * x = 0 := by ring

theorem distinct_readings_of_equal_norm_exclude_norm_factorization
    {A B C : Type*} (normMap : A → B) (reading : A → C) {x y : A}
    (equalNorms : normMap x = normMap y) (differentReadings : reading x ≠ reading y) :
    ¬ ∃ f : B → C, ∀ a, reading a = f (normMap a) := by
  rintro ⟨f, hf⟩
  exact differentReadings ((hf x).trans ((congrArg f equalNorms).trans (hf y).symm))

#print axioms nonzero_dyadic_multiplier
#print axioms residue_positive
#print axioms linear_centering_cancels
#print axioms distinct_readings_of_equal_norm_exclude_norm_factorization

end DyadicPoleFilter
