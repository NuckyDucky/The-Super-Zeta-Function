import QuartetLeadingParts
import QuarterEuler

namespace SuperZeta.QuartetBandDominance
noncomputable section
open Real Complex UnitSpectrum QuartetLeading
open scoped ComplexConjugate

private theorem exponent_re (s : ℂ) : (-2*s).re = -2*s.re := by simp [Complex.mul_re]
private theorem exponent_im (s : ℂ) : (-2*s).im = -2*s.im := by simp [Complex.mul_im]

/-- Norm of the first-root component at an arbitrary input, retaining its actual phase. -/
theorem leading_norm (s : ℂ) :
    ‖first ^ (-2*s)‖ = (‖first‖^(2*s.re))⁻¹ * Real.exp (2*s.im*first.arg) := by
  rw [Complex.norm_cpow_of_ne_zero first_ne_zero, exponent_re, exponent_im, neg_mul,
    Real.rpow_neg (norm_nonneg _), div_eq_mul_inv, ←Real.exp_neg]
  congr 2
  ring

private theorem three_quarters : (4:ℝ)^(3/4:ℝ) ≤ 3 := by
  have h := Real.rpow_mul_natCast (x:=4) (by norm_num) (3/4:ℝ) 4
  norm_num at h
  by_contra! br
  have hh := pow_lt_pow_left₀ br (by norm_num : 0≤(3:ℝ)) (by decide : (4:ℕ) ≠ 0)
  norm_num at hh
  linarith

theorem band_leading_lower {s : ℂ} (hr : s.re ≤ 9/32) (ht : 0 ≤ s.im) :
    Real.exp (5*s.im/4)/3 ≤ ‖first ^(-2*s)‖ := by
  have hnorm : 1 ≤ ‖first‖ := first_re_ge_one.trans (Complex.re_le_norm _)
  have hp : 0< ‖first‖^(2*s.re) := Real.rpow_pos_of_pos (by linarith) _
  have hb : ‖first‖^(2*s.re) ≤ 3 := calc
    _ ≤ ‖first‖^(3/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hnorm (by linarith)
    _ ≤ (4:ℝ)^(3/4:ℝ) := Real.rpow_le_rpow (norm_nonneg _) bounds.2.le (by norm_num)
    _ ≤ _ := three_quarters
  rw [leading_norm]
  have hi : (1/3:ℝ) ≤ (‖first‖^(2*s.re))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hp]
    norm_num
    exact hb
  have he : Real.exp (5*s.im/4) ≤ Real.exp (2*s.im*first.arg) := Real.exp_le_exp.mpr
    (by nlinarith only [mul_nonneg ht (sub_nonneg.mpr bounds.1.le)])
  linarith only [mul_le_mul hi he (Real.exp_pos _).le (inv_nonneg.mpr hp.le)]

theorem band_small_conjugate {s : ℂ} (hs : 0 ≤ s.re) (ht : 0 ≤ s.im) :
    ‖conj first ^(-2*s)‖ ≤ 1 := by
  have hp : first.arg ≠ π := by
    have := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (lt_of_lt_of_le zero_lt_one first_re_ge_one))
    linarith [Real.pi_pos]
  rw [Complex.norm_cpow_of_ne_zero (by simpa using first_ne_zero), exponent_re, exponent_im,
    Complex.arg_conj, if_neg hp, Complex.norm_conj, div_le_one (Real.exp_pos _)]
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (first_re_ge_one.trans (Complex.re_le_norm _))
    (show -2*s.re≤0 by linarith)
  apply hpow.trans
  apply Real.one_le_exp
  have ha : 0 ≤ first.arg := by linarith [bounds.1]
  nlinarith [mul_nonneg ha ht]

theorem dottie_lo : (1/4:ℝ) ≤ dottie := by
  by_contra! hh
  have cm := Real.cos_le_cos_of_nonneg_of_le_pi dottie_spec.1.1.le
      (show (1/4:ℝ) ≤ π by linarith [pi_gt_three]) hh.le
  have cv := (abs_le.mp (Real.cos_bound (x:=(1/4:ℝ)) (by
    rw [abs_of_nonneg (by norm_num : 0≤(1/4:ℝ))]; norm_num))).1
  rw [abs_of_nonneg (by norm_num : 0≤(1/4:ℝ))] at cv
  norm_num at cv
  linarith [dottie_spec.2]

theorem band_dottie {s : ℂ} (hr : s.re ≤ 9/32) :
    ‖(dottie:ℂ)^(-2*s)‖ ≤ 4 := by
  have hi : dottie ≤ 1 := dottie_spec.2.trans_le (Real.cos_le_one _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos dottie_spec.1.1, exponent_re]
  calc
    _ ≤ dottie^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge dottie_spec.1.1 hi (by linarith)
    _ ≤ _ := by rw [Real.rpow_neg_one, inv_le_comm₀ dottie_spec.1.1 (by norm_num)]; linarith [dottie_lo]

theorem band_pi {s : ℂ} (hl : 0 ≤ s.re) : ‖(π:ℂ)^(-2*s)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,exponent_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)

/-- The floor-integral formula bounds the ordinary zeta contribution throughout this band. -/
theorem band_zeta {w : ℂ} (hl : 7/16 ≤ w.re) (hr : w.re ≤ 9/16) (hi : 1 ≤ w.im) :
    ‖riemannZeta w‖ ≤ 2+3*‖w‖ := by
  have hp : 0<w.re := by linarith
  have him : 0 < (w-1).im := by simp; linarith
  have hden : 0 < ‖w-1‖ := him.trans_le (Complex.im_le_norm _)
  have hw : ‖w‖ ≤ 2*‖w-1‖ := by
    have hn := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos hp,abs_of_nonneg (show 0 ≤ w.im by linarith)] at hn
    have hd := Complex.im_le_norm (w-1)
    simp at hd
    linarith
  have hb := QuarterEuler.kernel_norm_le w hp
  have hb' : 1/w.re ≤ 3 := (div_le_iff₀ hp).mpr (by linarith)
  rw [QuarterEuler.zeta_integral hp (by linarith)]
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_mul]
  nlinarith only [(div_le_iff₀ hden).mpr hw, mul_le_mul_of_nonneg_left (hb.trans hb') (norm_nonneg w)]

end
end SuperZeta.QuartetBandDominance
