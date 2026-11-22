import Mathlib.Data.Complex.Trigonometric
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SuperZeta.GaussianSideConstants

/-- Bound both exponentials in sinh(0.9) with eight Taylor terms and
mathlib's proved remainder bound. -/
theorem sinh_ratio :
    Real.sinh (9/10) / (9/10) - 1 < (1406/10000 : ℝ) := by
  have hab : |(9/10 : ℝ)| = 9/10 := abs_of_nonneg (by norm_num)
  have han : |(-9/10 : ℝ)| = 9/10 := by rw [neg_div, abs_neg, hab]
  have hp := Real.exp_bound (x := (9/10 : ℝ)) (n := 8) (by rw [hab]; norm_num) (by decide)
  have hn := Real.exp_bound (x := (-9/10 : ℝ)) (n := 8) (by rw [han]; norm_num) (by decide)
  have hu := (abs_le.mp hp).2
  have hl := (abs_le.mp hn).1
  rw [hab] at hu
  rw [han] at hl
  norm_num [Finset.sum_range_succ, Nat.factorial] at hu hl
  rw [Real.sinh_eq]
  linarith

end SuperZeta.GaussianSideConstants
