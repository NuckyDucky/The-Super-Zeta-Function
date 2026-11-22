import SuperZeta.QuarterLine.QuartetLeading

namespace SuperZeta.QuartetLeading
noncomputable section
open Real Complex UnitSpectrum
open scoped ComplexConjugate

theorem first_re_ge_one : 1 ≤ first.re := by
  have h := RootBounds.x_lower (n:=1) (by decide)
    (by simpa using (levelHeight_spec 0).2)
  simpa [first, RootBounds.u] using h

theorem norm_conjugate_leading (t : ℝ) :
    ‖(conj first) ^ (-2 * (⟨1/4,t⟩ : ℂ))‖ =
      ‖first ^ (-2 * (⟨1/4,-t⟩ : ℂ))‖ := by
  have h : first.arg ≠ π := by
    have := Complex.arg_lt_pi_div_two_iff.mpr
      (Or.inl (lt_of_lt_of_le zero_lt_one first_re_ge_one))
    linarith [Real.pi_pos]
  have hz : conj first ≠ 0 := by simpa using first_ne_zero
  rw [norm_leading, Complex.norm_cpow_of_ne_zero hz, Complex.arg_conj, if_neg h]
  have hr : (-2 * (⟨1/4,t⟩ : ℂ)).re = -(1/2 : ℝ) := by norm_num [Complex.mul_re]
  have hi : (-2 * (⟨1/4,t⟩ : ℂ)).im = -2*t := by norm_num [Complex.mul_im]
  rw [hr,hi, Complex.norm_conj, Real.rpow_neg (norm_nonneg _), ← Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

theorem small_first {t : ℝ} (ht : t ≤ 0) :
    ‖first ^ (-2 * (⟨1/4,t⟩ : ℂ))‖ ≤ 1 := by
  rw [norm_leading]
  have hnorm : 1 ≤ ‖first‖ := first_re_ge_one.trans (Complex.re_le_norm _)
  have hs : 1 ≤ Real.sqrt ‖first‖ := by simpa using Real.sqrt_le_sqrt hnorm
  have hf : (Real.sqrt ‖first‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (2*t*first.arg) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [bounds.1])
  simpa using mul_le_mul hf he (exp_pos _).le zero_le_one

theorem dottie_power_le (t : ℝ) :
    ‖(dottie:ℂ)^(-2 * (⟨1/4,t⟩ : ℂ))‖ ≤ 2 := by
  have hp := dottie_spec.1.1
  have hd : (1/4:ℝ) ≤ dottie := by
    by_contra! hh
    have cm := Real.cos_le_cos_of_nonneg_of_le_pi hp.le
      (show (1/4:ℝ) ≤ π by linarith [pi_gt_three]) hh.le
    have cv := (abs_le.mp (Real.cos_bound (x:=(1/4:ℝ)) (by rw [abs_of_nonneg (by norm_num : 0≤(1/4:ℝ))]; norm_num))).1
    rw [abs_of_nonneg (by norm_num : 0≤(1/4:ℝ))] at cv
    norm_num at cv
    linarith [dottie_spec.2]
  have hs : (1/2:ℝ) ≤ Real.sqrt dottie := by
    have h := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, show Real.sqrt 4 = 2 by exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)] at h
    exact h
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : (-2 * (⟨1/4,t⟩ : ℂ)).re = -(1/2 : ℝ) := by norm_num [Complex.mul_re]
  rw [hr,Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity) (by norm_num)]
  norm_num
  exact hs

theorem pi_power_le (t : ℝ) :
    ‖(π:ℂ)^(-2 * (⟨1/4,t⟩ : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    (by norm_num [Complex.mul_re])

end
end SuperZeta.QuartetLeading
