import DottieSharpRelativeCircle

/-! A single small-error exponent for the relative completion on and inside
the original Dottie measuring circle and its reflection. -/

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open private log_scale_enclosure from DottieCompletedReferencePhase
open scoped ComplexConjugate
set_option autoImplicit false

noncomputable def dottieSharpExponentSlope : ℂ :=
  ⟨43.45042342189746392492, 1.57079632679489661923⟩

private theorem reference_re : dottieReferencePoint.re = 1/2 := by
  norm_num [dottieReferencePoint, mul_re]

private theorem reference_im : dottieReferencePoint.im = dottieHeight - 1/512 := by
  norm_num [dottieReferencePoint, mul_im]

private theorem reference_norm_gt : (4*10^12 : ℝ) < ‖dottieReferencePoint‖ := by
  have ht := dottieHeight_enclosure.1
  have hi := (le_abs_self dottieReferencePoint.im).trans (abs_im_le_norm _)
  rw [reference_im] at hi
  linarith only [hi,ht]

private theorem reference_arg_by_half_pi :
    0 ≤ Real.pi/2 - dottieReferencePoint.arg ∧
      Real.pi/2 - dottieReferencePoint.arg ≤ 2/10^13 := by
  let z := dottieReferencePoint
  have him : 0 ≤ z.im := by rw [show z.im = _ from reference_im]; linarith [dottieHeight_enclosure.1]
  have harg₀ : 0 ≤ z.arg := arg_nonneg_iff.mpr him
  have harg₁ : z.arg ≤ Real.pi/2 := arg_le_pi_div_two_iff.mpr (Or.inl (by
    change 0 ≤ dottieReferencePoint.re
    rw [reference_re]
    norm_num))
  have hne : z ≠ 0 := norm_ne_zero_iff.mp
    (lt_trans (by norm_num : (0:ℝ) < 4*10^12) reference_norm_gt).ne'
  let r := Real.pi/2-z.arg
  have hr : 0 ≤ r := sub_nonneg.mpr harg₁
  have hj := Real.mul_le_sin (x := r) hr (by dsimp only [r]; linarith only [harg₀])
  change 2/Real.pi*r ≤ Real.sin (Real.pi/2-z.arg) at hj
  rw [Real.sin_pi_div_two_sub, cos_arg hne, show z.re = 1/2 from reference_re] at hj
  have hcos : (1/2 : ℝ)/‖z‖ ≤ 1/(8*10^12) := by
    apply (div_le_iff₀ (by linarith only [reference_norm_gt] : 0 < ‖z‖)).2
    change (1/2 : ℝ) ≤ 1/(8*10^12)*‖dottieReferencePoint‖
    linarith only [reference_norm_gt]
  have hrate : (5/8 : ℝ) ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith only [Real.pi_lt_d20]
  have h := (mul_le_mul_of_nonneg_right hrate hr).trans (hj.trans hcos)
  refine ⟨hr,?_⟩
  change r ≤ 2/10^13
  linarith only [h]

theorem dottie_sharp_exponent_slope_error :
    ‖(Real.log archivedThetaScale : ℂ) + Complex.log dottieReferencePoint -
      dottieSharpExponentSlope‖ ≤ 1/10^12 := by
  let c := (Real.log archivedThetaScale : ℂ) + Complex.log dottieReferencePoint -
    dottieSharpExponentSlope
  apply (norm_le_abs_re_add_abs_im c).trans
  have hre : |c.re| ≤ 1/10^13 := by
    simp only [c,Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.log_re,dottieSharpExponentSlope]
    have h := dottie_reference_norm_log_interval
    change 29.14088602657451053933 < Real.log ‖dottieReferencePoint‖ ∧
      Real.log ‖dottieReferencePoint‖ < 29.14088602657451053934 at h
    exact abs_le.mpr ⟨by linarith only [h.1,log_scale_enclosure.1],
      by linarith only [h.2,log_scale_enclosure.2]⟩
  have him : |c.im| ≤ 3/10^13 := by
    simp only [c,Complex.sub_im,Complex.add_im,Complex.ofReal_im,zero_add,Complex.log_im,dottieSharpExponentSlope]
    obtain ⟨h₀,h₁⟩ := reference_arg_by_half_pi
    exact abs_le.mpr ⟨by linarith only [h₁,Real.pi_gt_d20],by linarith only [h₀,Real.pi_lt_d20]⟩
  linarith only [hre,him]

theorem dottie_sharp_relative_factor_affine {w : ℂ}
    (hw : ‖w-dottieReferencePoint‖ ≤ 1/25) :
    ∃ e : ℂ, ‖e‖ ≤ 1/10^12 ∧ dottieSharpRelativeFactor w =
      Complex.exp ((w-dottieReferencePoint)*dottieSharpExponentSlope + e) := by
  let z := dottieReferencePoint
  let d := w-z
  let q := d/z
  change ‖d‖ ≤ 1/25 at hw
  have hz : (4*10^12 : ℝ) < ‖z‖ := reference_norm_gt
  have hz₀ : 0 < ‖z‖ := by linarith only [hz]
  have hi₀ : (4*10^12+1 : ℝ) < z.im := by
    rw [show z.im = _ from reference_im]
    linarith only [dottieHeight_enclosure.1]
  have hi₁ : (4*10^12 : ℝ) < w.im := by
    have h : -d.im ≤ 1/25 := (neg_le_abs _).trans ((abs_im_le_norm d).trans hw)
    change -(w.im-z.im) ≤ 1/25 at h
    linarith only [hi₀,h]
  have hwr : 0 < w.re := by
    have h : -d.re ≤ 1/25 := (neg_le_abs _).trans ((abs_re_le_norm d).trans hw)
    change -(w.re-z.re) ≤ 1/25 at h
    rw [show z.re = 1/2 from reference_re] at h
    linarith only [h]
  have hq : ‖q‖ ≤ 1/10^14 := by
    rw [show ‖q‖ = ‖d‖/‖z‖ from norm_div d z]
    exact (div_le_iff₀ hz₀).2 (by linarith only [hz,hw])
  have hsmall : ‖q‖ ≤ 1/2 := hq.trans (by norm_num)
  obtain ⟨s,hs,hs_eq⟩ := dottie_sharp_relative_factor_stable hwr
    (by linarith only [hi₁,le_abs_self w.im]) hsmall
  have hprod : ‖z‖*‖q‖ = ‖d‖ := by
    change ‖z‖*‖d/z‖ = _
    rw [norm_div,mul_div_cancel₀ _ hz₀.ne']
  have hnormw : ‖w-1/2‖ ≤ 2*‖z‖ := by
    rw [show w-1/2 = d+(z-1/2) by dsimp only [d]; ring]
    have hr := norm_sub_le z (1/2)
    norm_num [norm_div] at hr
    exact (norm_add_le _ _).trans (by linarith only [hw,hr,hz])
  have hqerr : ‖w-1/2‖*‖q‖^2 ≤ 1/10^15 := by
    calc
      _ ≤ (2*‖z‖)*‖q‖^2 := mul_le_mul_of_nonneg_right hnormw (sq_nonneg _)
      _ = (2*‖d‖)*‖q‖ := by rw [← hprod]; ring
      _ ≤ (2*(1/25 : ℝ))*(1/10^14) := by gcongr
      _ ≤ _ := by norm_num
  have hRE (t : ℝ) (ht : (4*10^12 : ℝ) < t) : (1:ℝ)/(3*|t|) ≤ 1/10^13 := by
    have hp : 0 < t := by linarith only [ht]
    rw [abs_of_pos hp]
    apply (div_le_iff₀ (by positivity)).2
    linarith only [ht]
  have hs' : ‖s‖ ≤ 21/10^14 := by
    change ‖s‖ ≤ 1/(3*|z.im|)+1/(3*|w.im|)+‖w-1/2‖*‖q‖^2 at hs
    linarith only [hs,hqerr,hRE z.im (by linarith only [hi₀]),hRE w.im hi₁]
  have hqcor : ‖(d-1/2)*q‖ ≤ 6/10^15 := by
    rw [norm_mul]
    have hd := norm_sub_le d (1/2)
    norm_num [norm_div] at hd
    calc
      _ ≤ (27/50 : ℝ)*(1/10^14) := by
        exact mul_le_mul (by linarith only [hd,hw]) hq (norm_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  let E := (Real.log archivedThetaScale : ℂ) + Complex.log z - dottieSharpExponentSlope
  have hdE : ‖d*E‖ ≤ (1/25 : ℝ)*(1/10^12) := by
    rw [norm_mul]
    exact mul_le_mul hw dottie_sharp_exponent_slope_error (norm_nonneg _) (by norm_num)
  refine ⟨d*E + (d-1/2)*q + s, ?_, ?_⟩
  · exact (norm_add_le _ _).trans (by linarith only [norm_add_le (d*E) ((d-1/2)*q),hdE,hqcor,hs'])
  · rw [hs_eq]
    congr 1
    change (Real.log archivedThetaScale : ℂ)*d+d*Complex.log z+(d-1/2)*q+s =
      d*dottieSharpExponentSlope+(d*E+(d-1/2)*q+s)
    dsimp only [E]
    ring

private theorem exp_norm_le_nine {p : ℂ} (hnorm : ‖p‖ ≤ 2) : ‖Complex.exp p‖ ≤ 9 := by
  have h := (norm_exp_le_exp_norm p).trans (Real.exp_le_exp.mpr hnorm)
  have h₁ : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc
    _ ≤ Real.exp 2 := h
    _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ (3:ℝ)*3 := mul_le_mul h₁ h₁ (Real.exp_pos 1).le (by norm_num)
    _ = _ := by norm_num

theorem dottie_sharp_exponent_slope_norm : ‖dottieSharpExponentSlope‖ ≤ 46 :=
  (norm_le_abs_re_add_abs_im _).trans (by norm_num [dottieSharpExponentSlope])

private theorem affine_input_norm {w : ℂ} (hw : ‖w-dottieReferencePoint‖ ≤ 1/25) :
    ‖(w-dottieReferencePoint)*dottieSharpExponentSlope‖ ≤ 46/25 := by
  rw [norm_mul]
  calc
    _ ≤ (1/25 : ℝ)*46 := mul_le_mul hw dottie_sharp_exponent_slope_norm (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem dottie_sharp_relative_factor_norm_le_nine {w : ℂ}
    (hw : ‖w-dottieReferencePoint‖ ≤ 1/25) : ‖dottieSharpRelativeFactor w‖ ≤ 9 := by
  obtain ⟨e,he,hEq⟩ := dottie_sharp_relative_factor_affine hw
  rw [hEq]
  exact exp_norm_le_nine ((norm_add_le _ _).trans (by linarith only [affine_input_norm hw,he]))

theorem dottie_sharp_relative_factor_sub_affine {w : ℂ}
    (hw : ‖w-dottieReferencePoint‖ ≤ 1/25) :
    ‖dottieSharpRelativeFactor w-Complex.exp ((w-dottieReferencePoint)*dottieSharpExponentSlope)‖ ≤
      18/10^12 := by
  obtain ⟨e,he,hEq⟩ := dottie_sharp_relative_factor_affine hw
  let p := (w-dottieReferencePoint)*dottieSharpExponentSlope
  have hp : ‖p‖ ≤ 2 := by linarith only [affine_input_norm hw]
  have he' : ‖e‖ ≤ 1 := he.trans (by norm_num)
  change ‖dottieSharpRelativeFactor w-Complex.exp p‖ ≤ _
  rw [hEq]
  change ‖Complex.exp (p+e)-Complex.exp p‖ ≤ _
  rw [Complex.exp_add,show Complex.exp p*Complex.exp e-Complex.exp p =
    Complex.exp p*(Complex.exp e-1) by ring,norm_mul]
  calc
    _ ≤ (9:ℝ)*(2*‖e‖) :=
      mul_le_mul (exp_norm_le_nine hp) (norm_exp_sub_one_le he') (norm_nonneg _) (by norm_num)
    _ ≤ _ := by linarith only [he]

theorem dottie_sharp_affine_domain_on_circle {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖w-dottieReferencePoint‖ ≤ 1/25 ∧
      ‖(1-conj w)-dottieReferencePoint‖ ≤ 1/25 := by
  let c := archivedRightCenter dottieHeight
  let r := dottieReferencePoint
  have hr : ‖w-c‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hc : c-r = (1/64 : ℂ) := by
    apply Complex.ext <;> norm_num [c,r,archivedRightCenter,dottieReferencePoint,mul_re,mul_im]
  have hm : 1-conj r = r := by
    apply Complex.ext <;> norm_num [r,dottieReferencePoint,mul_re,mul_im]
  have hn : ‖w-r‖ ≤ 1/25 := by
    rw [show w-r = (w-c)+(c-r) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [hr,hc]
    norm_num [norm_div,Complex.norm_ofNat]
  have hd : (1-conj w)-r = -conj (w-r) := by
    rw [map_sub]
    linear_combination hm
  exact ⟨hn,by rwa [hd,norm_neg,Complex.norm_conj]⟩

theorem dottie_sharp_pair_norm_le_eighteen {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieSharpRelativeFactor w‖+‖dottieSharpRelativeFactor (1-conj w)‖ ≤ 18 := by
  obtain ⟨h,h'⟩ := dottie_sharp_affine_domain_on_circle hw
  linarith only [dottie_sharp_relative_factor_norm_le_nine h,
    dottie_sharp_relative_factor_norm_le_nine h']

#print axioms dottie_sharp_exponent_slope_error
#print axioms dottie_sharp_relative_factor_affine
#print axioms dottie_sharp_relative_factor_norm_le_nine
#print axioms dottie_sharp_relative_factor_sub_affine
#print axioms dottie_sharp_affine_domain_on_circle
#print axioms dottie_sharp_pair_norm_le_eighteen

end QuarticModel
