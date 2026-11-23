import DottieHighGammaLocal
import DottieReferenceMoment

/-! A lower bound for the Gamma ratio in the original reference normalization. -/

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open private arctan_bounds arg_quarter_sub_arctan stirling_leading_re from DottieHighGammaLocal

theorem dottie_reference_gamma_norm_ratio_lower :
    dottieHeight ^ (-(3/2 : ℝ)) ≤
      ‖Gamma dottieReferencePoint‖ / ‖Gamma (2+(dottieHeight : ℂ)*I)‖ := by
  let T := dottieHeight
  let t := T-1/512
  let w := dottieReferencePoint
  let z : ℂ := 2+(T : ℂ)*I
  have hT : (4*10^12 : ℝ) < T := by
    dsimp only [T]
    linarith only [dottieHeight_enclosure.1]
  have ht : (3*10^12 : ℝ) < t := by dsimp only [t]; linarith only [hT]
  have hT_pos : 0 < T := by linarith only [hT]
  have ht_pos : 0 < t := by linarith only [ht]
  have hw_re : w.re = 1/2 := by norm_num [w, dottieReferencePoint, Complex.mul_re]
  have hw_im : w.im = t := by simp [w, dottieReferencePoint, t, T, Complex.mul_im]
  have hz_re : z.re = 2 := by simp [z, Complex.mul_re]
  have hz_im : z.im = T := by simp [z, Complex.mul_im]
  have hw_re_pos : 0 < w.re := by rw [hw_re]; norm_num
  have hz_re_pos : 0 < z.re := by rw [hz_re]; norm_num
  have hw_im_pos : 0 < w.im := by rw [hw_im]; exact ht_pos
  have hz_im_pos : 0 < z.im := by rw [hz_im]; exact hT_pos
  obtain ⟨e,he,hGamma⟩ := dottie_gamma_ratio_with_error hz_re_pos hw_re_pos
    (show 1 ≤ |z.im| by rw [hz_im, abs_of_pos hT_pos]; linarith only [hT])
    (show 1 ≤ |w.im| by rw [hw_im, abs_of_pos ht_pos]; linarith only [ht])
  have he_re : -(1/10^12 : ℝ) ≤ e.re := by
    rw [hz_im, hw_im, abs_of_pos hT_pos, abs_of_pos ht_pos] at he
    have h₁ : 1/(3*T) ≤ (1/10^12 : ℝ)/2 :=
      (div_le_iff₀ (by positivity)).2 (by linarith only [hT])
    have h₂ : 1/(3*t) ≤ (1/10^12 : ℝ)/2 :=
      (div_le_iff₀ (by positivity)).2 (by linarith only [ht])
    linarith only [(abs_le.mp ((Complex.abs_re_le_norm e).trans he)).1,h₁,h₂]

  have hz_norm_upper : ‖z‖ ≤ T+2 := by
    calc
      ‖z‖ ≤ ‖(2 : ℂ)‖+‖(T : ℂ)*I‖ := norm_add_le _ _
      _ = T+2 := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT_pos, add_comm]
  have hz_norm_pos : 0 < ‖z‖ := hT_pos.trans_le (by
    simpa only [hz_im, abs_of_pos hT_pos] using Complex.abs_im_le_norm z)
  have hlog_z : Real.log ‖z‖ ≤ Real.log T+2/T := by
    refine (Real.log_le_log hz_norm_pos hz_norm_upper).trans ?_
    have h := Real.log_le_sub_one_of_pos (show 0 < (T+2)/T by positivity)
    have heq : (T+2)/T-1 = 2/T := by
      field_simp [hT_pos.ne']
      ring
    rw [Real.log_div (by positivity) hT_pos.ne', heq] at h
    linarith only [h]

  have hw_angle : -(1/10^12 : ℝ) ≤ t*Real.arctan ((1/2)/t)-1/2 := by
    have h := mul_le_mul_of_nonneg_left
      (arctan_bounds (show 0 ≤ (1/2)/t by positivity)).1 ht_pos.le
    have heq : t*((1/2)/t-((1/2)/t)^3/3)-1/2 = -(1/(24*t^2)) := by
      field_simp [ht_pos.ne']
      ring
    have hsmall : 1/(24*t^2) ≤ (1/10^12 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3*10^12) ht.le 2
      linarith only [hs]
    linarith only [h,heq,hsmall]
  have hz_angle : T*Real.arctan (2/T)-2 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left
      (arctan_bounds (show 0 ≤ 2/T by positivity)).2 hT_pos.le
    have heq : T*(2/T) = 2 := by field_simp [hT_pos.ne']
    linarith only [h,heq]

  have hw_lead : -t*(Real.pi/2)-1/10^12 ≤ (dottieStirlingLeading w).re := by
    rw [stirling_leading_re, arg_quarter_sub_arctan hw_re_pos hw_im_pos, hw_re, hw_im]
    nlinarith only [hw_angle]
  have hz_lead : (dottieStirlingLeading z).re ≤
      (3/2 : ℝ)*(Real.log T+2/T)-T*(Real.pi/2) := by
    rw [stirling_leading_re, arg_quarter_sub_arctan hz_re_pos hz_im_pos, hz_re, hz_im]
    nlinarith only [mul_le_mul_of_nonneg_left hlog_z (by norm_num : (0 : ℝ) ≤ 3/2), hz_angle]
  have hsmall : (3/2 : ℝ)*(2/T) ≤ 1/10^12 := by
    rw [show (3/2 : ℝ)*(2/T) = 3/T by ring]
    exact (div_le_iff₀ hT_pos).2 (by linarith only [hT])
  have hgain : (3/10^12 : ℝ) ≤ Real.pi/1024 := by linarith only [Real.pi_gt_three]
  have hlead : Real.log T * (-(3/2 : ℝ)) ≤
      (dottieStirlingLeading w).re-(dottieStirlingLeading z).re+e.re := by
    dsimp only [t] at hw_lead
    nlinarith only [hw_lead,hz_lead,hsmall,he_re,hgain]
  change T ^ (-(3/2 : ℝ)) ≤ ‖Gamma w‖ / ‖Gamma z‖
  rw [Real.rpow_def_of_pos hT_pos, ← norm_div, hGamma, Complex.norm_exp,
    Complex.add_re, Complex.sub_re]
  exact Real.exp_le_exp.mpr hlead

#print axioms dottie_reference_gamma_norm_ratio_lower

end QuarticModel
