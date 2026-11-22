import Mathlib.Data.Complex.ExponentialBounds
import SuperZeta.UnitSpectrum

namespace SuperZeta.QuarterScalar

theorem band_margin {t : ℝ} (ht : 100 ≤ t) :
    128*3*70*(t+2) < Real.exp (3*t/20) := by
  have h15 : (3000000:ℝ) ≤ Real.exp 15 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.71)
      (show (2.71:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 15
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    linarith
  let x := 3*(t-100)/20
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have he := mul_le_mul h15 (Real.add_one_le_exp x) (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add, show 15+x=3*t/20 by dsimp [x]; ring] at he
  dsimp [x] at he
  linarith

end SuperZeta.QuarterScalar
