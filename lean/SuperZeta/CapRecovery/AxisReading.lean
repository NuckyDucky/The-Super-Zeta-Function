import SuperZeta.CapRecovery.Resonant

/-! Observable used to read the unsigned lift directly from the derivative
ratio. For a single stage the reading lies on an axis. -/
noncomputable section
namespace SuperZeta.AxisReading

open Complex Resonant

def axisRatio (z : ℂ) : ℝ :=
  max |z.re| |z.im| / min |z.re| |z.im|

def estimate (z : ℂ) : ℝ := if axisRatio z = 0 then ‖z‖ else axisRatio z

theorem estimate_axis {z : ℂ} (h : z.re = 0 ∨ z.im = 0) :
    estimate z = ‖z‖ := by
  rcases h with h | h <;> simp [estimate, axisRatio, h, abs_nonneg]

theorem base_imag (m : ℤ) : base m = ((base m).im : ℂ) * I := by
  rcases phase_cases m with h | h <;>
    apply Complex.ext <;> simp [base, Resonant.lift, h, Complex.mul_re, Complex.mul_im]

theorem abs_im_base (m : ℤ) : |(base m).im| = ‖base m‖ := by
  conv_rhs => rw [base_imag m]
  simp [norm_mul]

theorem axisRatio_real_mul (u : ℝ) (hu : u ≠ 0) (z : ℂ) :
    axisRatio ((u:ℂ) * z) = axisRatio z := by
  simp only [axisRatio, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg u),
    ← mul_min_of_nonneg _ _ (abs_nonneg u)]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr hu)

theorem axisRatio_I (z : ℂ) : axisRatio (I*z) = axisRatio z := by
  simp [axisRatio, max_comm, min_comm]

theorem axisRatio_base_mul (m : ℤ) (hm : m ≠ 0) (z : ℂ) :
    axisRatio (base m * z) = axisRatio z := by
  have hu : (base m).im ≠ 0 := by
    intro h
    apply base_ne_zero hm
    simpa [h] using base_imag m
  calc
    axisRatio (base m * z) = axisRatio (((base m).im:ℂ) * (I*z)) := by
      conv_lhs => rw [base_imag m, mul_assoc]
    _ = _ := (axisRatio_real_mul _ hu _).trans (axisRatio_I z)

theorem axisRatio_scaled_reverse (m : ℤ) (hm : m ≠ 0) (n : ℕ) (z : ℂ) :
    axisRatio (phase m * ((base m)^n * z)) = axisRatio z := by
  have hpow : axisRatio ((base m)^n*z) = axisRatio z := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, axisRatio_base_mul m hm, ih]
  rcases phase_cases m with h | h
  · simpa [h] using hpow
  · rw [h, ← Complex.ofReal_one, ← Complex.ofReal_neg, axisRatio_real_mul (-1) (by norm_num)]
    exact hpow

end SuperZeta.AxisReading
