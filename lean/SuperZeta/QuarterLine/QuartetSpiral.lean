import SuperZeta.QuarterLine.QuartetLeading

noncomputable section
open Complex Real
namespace SuperZeta.QuartetSpiral

open QuartetLeading

/-- The contribution of the first upper cosine root on the quarter-line. -/
def term (t : ℝ) : ℂ := first ^ (-2 * (⟨1/4,t⟩ : ℂ))

/-- The height increment corresponding to one full clockwise revolution. -/
def period : ℝ := Real.pi / Real.log ‖first‖

theorem norm_first_gt_one : 1 < ‖first‖ := by
  have h := (height_interval).1
  have hi : first.im = UnitSpectrum.levelHeight 0 := rfl
  have hb := Complex.im_le_norm first
  linarith

theorem period_pos : 0 < period :=
  div_pos Real.pi_pos (Real.log_pos norm_first_gt_one)

/-- The positive real factor changes the radius; the imaginary exponential
tracks a continuous change of argument through any number of full turns. -/
theorem term_shift (t h : ℝ) :
    term (t+h) = term t *
      (Real.exp (2*h*first.arg) : ℂ) *
      Complex.exp (((-2*h*Real.log ‖first‖ : ℝ) : ℂ)*Complex.I) := by
  simp only [term,Complex.cpow_def_of_ne_zero first_ne_zero,Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.log_re,
      Complex.log_im] <;> ring

theorem angular_change_neg {h : ℝ} (hh : 0 < h) : -2*h*Real.log ‖first‖ < 0 := by
  have := Real.log_pos norm_first_gt_one
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hh) this

theorem radius_multiplier_gt_one {h : ℝ} (hh : 0 < h) : 1 < Real.exp (2*h*first.arg) :=
  Real.one_lt_exp_iff.mpr (mul_pos (mul_pos (by norm_num) hh) (by linarith [bounds.1]))

theorem angular_change_one_turn : -2*period*Real.log ‖first‖ = -2*Real.pi := by
  unfold period
  field_simp [(Real.log_pos norm_first_gt_one).ne']

theorem term_after_clockwise_turn (t : ℝ) :
    term (t+period) = term t * (Real.exp (2*period*first.arg) : ℂ) := by
  rw [term_shift,angular_change_one_turn]
  have e : Complex.exp (((-2*Real.pi:ℝ):ℂ)*Complex.I) = 1 := by
    rw [show (((-2*Real.pi:ℝ):ℂ)*Complex.I) = -(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring,
      Complex.exp_neg,Complex.exp_two_pi_mul_I,inv_one]
  rw [e,mul_one]

end SuperZeta.QuartetSpiral
