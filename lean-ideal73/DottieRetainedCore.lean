import DottieLowerRightBound

/-! Integrate the retained polynomial bound on the core of the original
right contour, in the completion units of the Dottie circle. -/

namespace QuarticModel

open Complex Finset MeasureTheory Set SuperZeta.StirlingCorrection
open private dottieContour from ArchivedDottieTailPartition
set_option autoImplicit false
set_option maxRecDepth 4096

private theorem dottie_gamma_core_exp_le :
    Real.exp (35*Real.pi/4096+2/10^10) ≤ 21/20 := by
  have h : 35*Real.pi/4096+2/10^10 ≤ 1/21 := by linarith only [Real.pi_lt_four]
  exact (Real.exp_le_exp.mpr h).trans
    ((Real.exp_bound_div_one_sub_of_interval (x := 1/21) (by norm_num) (by norm_num)).trans
      (by norm_num))

private theorem dottie_right_core_integrand_bound (S : Finset ℕ) {w : ℂ} {u C : ℝ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048)) (hi : |w.im-dottieHeight| ≤ 35/2048)
    (hu : |u| ≤ 20)
    (hpoly : ‖dottieRangePolynomial S (w+dottieContour u)‖ *
      (dottieHeight^(w.re-1)/archivedThetaScale^2) ≤ C) :
    ‖dottieRangeIntegrand S w u / (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))‖ ≤
      C*((21/20)*(11/4)/6)*Real.exp (-u^2) := by
  let T := dottieHeight
  let B := archivedThetaScale
  let G := ‖Gamma (2+(T : ℂ)*I)‖
  let den : ℂ := 2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)
  let z := dottieContour u
  have hT : 0 < T := by dsimp only [T]; linarith only [dottieHeight_enclosure.1]
  have hden : ‖den‖ = 2*Real.pi*(B^2*G) := by
    have hd : den = ((2*Real.pi*archivedDottieCompletionScale : ℝ) : ℂ) := by
      dsimp only [den]
      norm_cast
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (mul_pos (by positivity) archivedDottieCompletionScale_pos)]
    rfl
  have hz₀ : z.re = 1 := by simp [z,dottieContour]
  have hz₁ : z.im = u := by simp [z,dottieContour]
  have hz : (1 : ℝ) ≤ ‖z‖ := by simpa [hz₀] using Complex.abs_re_le_norm z
  have hprod : (6 : ℝ) ≤ ‖z‖*(2*Real.pi) := by
    have hp : (6 : ℝ) ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
    simpa using mul_le_mul hz hp (by norm_num : (0 : ℝ) ≤ 6) (norm_nonneg z)
  have hs : w+z = ⟨w.re+1,w.im+u⟩ := by apply Complex.ext <;> simp [hz₀,hz₁]
  have hg : ‖Gamma (w+z)‖/G * Real.exp (Real.pi*u/2) ≤ T^(w.re-1)*(21/20) := by
    have h := dottie_gamma_shifted_tilted_norm_ratio 6 (by norm_num) hr hi hu
    rw [show w.re+7-(6 : ℕ) = w.re+1 by push_cast; ring,
      show w.re+5-(6 : ℕ) = w.re-1 by push_cast; ring] at h
    rw [hs]
    exact h.trans (mul_le_mul_of_nonneg_left dottie_gamma_core_exp_le
      (Real.rpow_nonneg hT.le _))
  have hexp : ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ =
      (Real.exp 1*Real.exp (-u^2))*Real.exp (Real.pi*u/2) := by
    have he : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
      simp [pow_two,Complex.mul_re,Complex.mul_im]
      ring
    rw [Complex.norm_exp,he,hz₀,hz₁,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  change ‖(dottieRangePolynomial S (w+z)*Gamma (w+z)*
      Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)/z)/den‖ ≤ _
  rw [norm_div,norm_div,norm_mul,norm_mul,hexp,hden]
  calc
    _ = (‖dottieRangePolynomial S (w+z)‖/B^2) *
        (‖Gamma (w+z)‖/G*Real.exp (Real.pi*u/2)) *
        (Real.exp 1*Real.exp (-u^2))/(‖z‖*(2*Real.pi)) := by ring
    _ ≤ (‖dottieRangePolynomial S (w+z)‖/B^2) * (T^(w.re-1)*(21/20)) *
        ((11/4)*Real.exp (-u^2))/6 := by
      apply div_le_div₀ (by positivity) ?_ (by norm_num) hprod
      gcongr
      linarith only [Real.exp_one_lt_d9]
    _ = (‖dottieRangePolynomial S (w+z)‖*(T^(w.re-1)/B^2))*
        ((21/20)*(11/4)/6)*Real.exp (-u^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (by norm_num))
      (Real.exp_pos _).le

theorem dottie_normalized_right_core_bound (S : Finset ℕ) {w : ℂ} {C : ℝ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (hC : 0 ≤ C)
    (hpoly : ∀ u ∈ Set.Ioc (-20 : ℝ) 20,
      ‖dottieRangePolynomial S (w+dottieContour u)‖ *
        (dottieHeight^(w.re-1)/archivedThetaScale^2) ≤ C) :
    ‖(∫ u in Set.Ioc (-20 : ℝ) 20, dottieRangeIntegrand S w u) /
      (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))‖ ≤ (7/8)*C := by
  let M := C*((21/20)*(11/4)/6)
  have hM : 0 ≤ M := mul_nonneg hC (by norm_num)
  have hb : Integrable (fun u : ℝ => M*Real.exp (-u^2)) := by
    simpa only [neg_mul,one_mul] using
      (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)).const_mul M
  rw [← MeasureTheory.integral_div]
  refine (MeasureTheory.norm_integral_le_of_norm_le hb.integrableOn ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact dottie_right_core_integrand_bound S hr hi (abs_le.mpr ⟨hu.1.le,hu.2⟩) (hpoly u hu)
  · refine (setIntegral_le_integral hb (Filter.Eventually.of_forall (fun u =>
        mul_nonneg hM (Real.exp_pos (-u^2)).le))).trans ?_
    rw [integral_const_mul]
    have hg : (∫ u : ℝ, Real.exp (-u^2)) = √Real.pi := by
      simpa only [neg_mul,one_mul,div_one] using integral_gaussian (1 : ℝ)
    rw [hg]
    have hπ : √Real.pi ≤ 9/5 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [Real.pi_lt_d4]⟩
    refine (mul_le_mul_of_nonneg_left hπ hM).trans ?_
    dsimp only [M]
    nlinarith only [hC]

theorem dottie_range_side_bound_of_core_mass (S : Finset ℕ) {w : ℂ} {C : ℝ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^19)
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (hC : 0 ≤ C)
    (hpoly : ∀ u ∈ Set.Ioc (-20 : ℝ) 20,
      ‖dottieRangePolynomial S (w+dottieContour u)‖ *
        (dottieHeight^(w.re-1)/archivedThetaScale^2) ≤ C) :
    ‖dottieRangeSide S w‖ ≤ (7/8)*C+1/10^79 := by
  have hw : 0 < w.re+1 := by linarith only [hr.1]
  have hn : ∀ n ∈ S, n ≠ 0 := fun n hn => (hS n hn).1.ne'
  have hsplit := integral_add_compl (s := Set.Ioc (-20 : ℝ) 20) measurableSet_Ioc
    (dottie_range_integrand_integrable S hw hn)
  rw [dottieRangeSide,← hsplit,add_div]
  exact (norm_add_le _ _).trans (add_le_add (dottie_normalized_right_core_bound S hr hi hC hpoly)
    (dottie_normalized_right_exterior_large_bound S hS hr hi))

#print axioms dottie_normalized_right_core_bound
#print axioms dottie_range_side_bound_of_core_mass

end QuarticModel
