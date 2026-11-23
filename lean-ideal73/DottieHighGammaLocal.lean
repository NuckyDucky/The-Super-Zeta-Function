import ArchivedDottieHeight
import DottieGammaRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! The Gamma ratio on the bounded vertical part of the shifted Dottie contour. -/

namespace QuarticModel

open Complex Set SuperZeta.StirlingCorrection

private theorem arctan_bounds {x : ℝ} (hx : 0 ≤ x) :
    x - x^3/3 ≤ Real.arctan x ∧ Real.arctan x ≤ x := by
  have upper := image_sub_le_mul_sub_of_deriv_le (C := 1) Real.differentiable_arctan
    (fun r => by
      rw [Real.deriv_arctan]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith only [sq_nonneg r])) hx
  let f := fun r : ℝ => Real.arctan r - (r - r^3/3)
  have hf (r : ℝ) : HasDerivAt f (1/(1+r^2) - (1-r^2)) r := by
    have hp : HasDerivAt (fun y : ℝ => y^3/3) (r^2) r := by
      have heq : (3 : ℝ) * r^((3 : ℕ)-1) * 1 / 3 = r^2 := by norm_num
      rw [← heq]
      exact ((hasDerivAt_id' r).pow 3).div_const (3 : ℝ)
    exact (Real.hasDerivAt_arctan r).sub ((hasDerivAt_id' r).sub hp)
  have hmono := monotone_of_deriv_nonneg (fun r => (hf r).differentiableAt) (fun r => by
    rw [(hf r).deriv, sub_nonneg]
    exact (le_div_iff₀ (by positivity)).2 (by nlinarith only [sq_nonneg (r^2)]))
  have hlower := hmono hx
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hlower
  exact ⟨sub_nonneg.mp hlower, by simpa [Real.arctan_zero] using upper⟩

private theorem arg_quarter_sub_arctan {z : ℂ} (hre : 0 < z.re) (him : 0 < z.im) :
    z.arg = Real.pi/2 - Real.arctan (z.re/z.im) := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
  calc
    z.arg = Real.arctan (Real.tan z.arg) := (Real.arctan_tan harg.1 harg.2).symm
    _ = Real.arctan ((z.re/z.im)⁻¹) := by rw [Complex.tan_arg, inv_div]
    _ = _ := Real.arctan_inv_of_pos (div_pos hre him)

private theorem stirling_leading_re (z : ℂ) :
    (dottieStirlingLeading z).re = (z.re-1/2)*Real.log ‖z‖ - z.im*z.arg - z.re := by
  norm_num [dottieStirlingLeading, Complex.mul_re, Complex.log_re, Complex.log_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The height-local Gamma ratio for the line `Re z = 7`, on both horizontal chords. -/
theorem dottie_gamma_k7_local_norm_ratio {σ t u : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048 : ℝ) (1/2+63/2048))
    (ht : |t-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20) :
    ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ / ‖Gamma (2+(dottieHeight : ℂ)*I)‖ ≤
      dottieHeight^(σ+5) * Real.exp (-Real.pi*(t+u-dottieHeight)/2+1/10^10) := by
  let T := dottieHeight
  let a := σ+7
  let b := t+u
  let w : ℂ := ⟨a,b⟩
  let z : ℂ := 2+(T : ℂ)*I
  have hT : (4*10^12 : ℝ) < T := by
    dsimp only [T]
    linarith only [dottieHeight_enclosure.1]
  have hT_pos : 0 < T := by linarith only [hT]
  have ha : 0 < a := by dsimp only [a]; linarith only [hσ.1]
  have ha_max : a ≤ 8 := by dsimp only [a]; linarith only [hσ.2]
  have ha_half : 0 ≤ a-1/2 := by dsimp only [a]; linarith only [hσ.1]
  have hb_diff : |b-T| ≤ 21 := by
    dsimp only [b,T]
    rw [show t+u-dottieHeight = (t-dottieHeight)+u by ring]
    exact (abs_add_le _ _).trans (by linarith only [ht,hu])
  have hb_min : (3*10^12 : ℝ) < b := by linarith only [(abs_le.mp hb_diff).1,hT]
  have hb : 0 < b := by linarith only [hb_min]
  have hb_max : b ≤ T+21 := by linarith only [(abs_le.mp hb_diff).2]
  have hz_re : z.re = 2 := by simp [z, Complex.mul_re]
  have hz_im : z.im = T := by simp [z, Complex.mul_im]
  have hz_pos : 0 < z.re := by rw [hz_re]; norm_num
  have hz_im_pos : 0 < z.im := by rw [hz_im]; exact hT_pos
  obtain ⟨e, he, hGamma⟩ := dottie_gamma_ratio_with_error hz_pos (show 0 < w.re from ha)
    (show 1 ≤ |z.im| by rw [hz_im, abs_of_pos hT_pos]; linarith only [hT])
    (show 1 ≤ |w.im| by change 1 ≤ |b|; rw [abs_of_pos hb]; linarith only [hb_min])
  have he_re : e.re ≤ 1/10^12 := by
    rw [hz_im, abs_of_pos hT_pos, show w.im = b from rfl, abs_of_pos hb] at he
    have h1 : 1/(3*T) ≤ (1/10^12 : ℝ)/2 :=
      (div_le_iff₀ (by positivity)).2 (by linarith only [hT])
    have h2 : 1/(3*b) ≤ (1/10^12 : ℝ)/2 :=
      (div_le_iff₀ (by positivity)).2 (by linarith only [hb_min])
    linarith only [(Complex.re_le_norm e).trans he,h1,h2]

  have hw_geom : w = (a : ℂ)+(b : ℂ)*I := by
    apply Complex.ext <;> simp [w, Complex.mul_re, Complex.mul_im]
  have hw_norm : ‖w‖ ≤ T+29 := by
    calc
      ‖w‖ = ‖(a : ℂ)+(b : ℂ)*I‖ := by rw [hw_geom]
      _ ≤ ‖(a : ℂ)‖+‖(b : ℂ)*I‖ := norm_add_le _ _
      _ = a+b := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
      _ ≤ T+29 := by linarith only [ha_max,hb_max]
  have hw_norm_pos : 0 < ‖w‖ := hb.trans_le (by
    simpa only [show w.im = b from rfl, abs_of_pos hb] using Complex.abs_im_le_norm w)
  have hz_norm : T ≤ ‖z‖ := by
    simpa only [hz_im, abs_of_pos hT_pos] using Complex.abs_im_le_norm z
  have hlog_z := Real.log_le_log hT_pos hz_norm
  have hlog_w : Real.log ‖w‖ ≤ Real.log T+29/T := by
    refine (Real.log_le_log hw_norm_pos hw_norm).trans ?_
    have h := Real.log_le_sub_one_of_pos (show 0 < (T+29)/T by positivity)
    have heq : (T+29)/T-1 = 29/T := by
      field_simp [hT_pos.ne']
      ring
    rw [Real.log_div (by positivity) hT_pos.ne', heq] at h
    linarith only [h]

  have hw_angle : b*Real.arctan (a/b)-a ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left (arctan_bounds (div_nonneg ha.le hb.le)).2 hb.le
    have heq : b*(a/b) = a := by field_simp [hb.ne']
    linarith only [h,heq]
  have hz_angle : -(1/10^12 : ℝ) ≤ T*Real.arctan (2/T)-2 := by
    have h := mul_le_mul_of_nonneg_left
      (arctan_bounds (show 0 ≤ 2/T by positivity)).1 hT_pos.le
    have heq : T*(2/T-(2/T)^3/3)-2 = -(8/(3*T^2)) := by
      field_simp [hT_pos.ne']
      ring
    have hsmall : (8 : ℝ)/(3*T^2) ≤ 1/10^12 := by
      apply (div_le_iff₀ (by positivity)).2
      have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4*10^12) hT.le 2
      linarith only [hs]
    linarith only [h,heq,hsmall]

  have hw_lead : (dottieStirlingLeading w).re ≤ (a-1/2)*(Real.log T+29/T)-b*(Real.pi/2) := by
    rw [stirling_leading_re, arg_quarter_sub_arctan (show 0 < w.re from ha) (show 0 < w.im from hb)]
    change (a-1/2)*Real.log ‖w‖-b*(Real.pi/2-Real.arctan (a/b))-a ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hlog_w ha_half, hw_angle]
  have hz_lead : (3/2 : ℝ)*Real.log T-T*(Real.pi/2)-1/10^12 ≤ (dottieStirlingLeading z).re := by
    rw [stirling_leading_re, arg_quarter_sub_arctan hz_pos hz_im_pos, hz_re, hz_im]
    nlinarith only [mul_le_mul_of_nonneg_left hlog_z (by norm_num : (0 : ℝ) ≤ 3/2), hz_angle]
  have hsmall : (a-1/2)*(29/T) ≤ (6/10^11 : ℝ) := by
    calc
      _ ≤ 8*(29/T) := mul_le_mul_of_nonneg_right (by linarith only [ha_max]) (by positivity)
      _ = 232/T := by ring
      _ ≤ _ := (div_le_iff₀ hT_pos).2 (by linarith only [hT])
  have hlead : (dottieStirlingLeading w).re-(dottieStirlingLeading z).re+e.re ≤
      Real.log T*(σ+5)+(-Real.pi*(b-T)/2+1/10^10) := by
    dsimp only [a] at hw_lead hsmall
    nlinarith only [hw_lead,hz_lead,hsmall,he_re]
  change ‖Gamma w‖ / ‖Gamma z‖ ≤ T^(σ+5)*Real.exp (-Real.pi*(b-T)/2+1/10^10)
  rw [← norm_div, hGamma, Complex.norm_exp, Complex.add_re, Complex.sub_re,
    Real.rpow_def_of_pos hT_pos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hlead

/-- The Gaussian contour's tilt cancels the dependence on `u` in the exponential. -/
theorem dottie_gamma_k7_local_tilted_norm_ratio {σ t u : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048 : ℝ) (1/2+63/2048))
    (ht : |t-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20) :
    (‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ / ‖Gamma (2+(dottieHeight : ℂ)*I)‖) *
      Real.exp (Real.pi*u/2) ≤ dottieHeight^(σ+5)*Real.exp (35*Real.pi/4096+1/10^10) := by
  refine (mul_le_mul_of_nonneg_right (dottie_gamma_k7_local_norm_ratio hσ ht hu)
    (Real.exp_pos _).le).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  have hT : 0 ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg hT _)
  have ht_low := mul_le_mul_of_nonneg_left (abs_le.mp ht).1 Real.pi_pos.le
  nlinarith only [ht_low]

#print axioms dottie_gamma_k7_local_norm_ratio
#print axioms dottie_gamma_k7_local_tilted_norm_ratio

end QuarticModel
