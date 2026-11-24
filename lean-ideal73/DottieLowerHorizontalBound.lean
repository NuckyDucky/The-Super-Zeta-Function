import DottieLowerLeftBound
import DottieLowerGammaHorizontal
import DottieFarNumeric

/-! Quantitative estimates on the two horizontal edges of the lower
smoothing rectangle. The Gaussian tilt supplies the small exponential. -/

namespace QuarticModel

open Complex Finset Set
open SuperZeta.StirlingCorrection
open private horizontalPoint from ArchivedDottieContourShift
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem lower_horizontal_power_mass_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {s : ℂ}
    (hr : -7 ≤ s.re) (hr' : s.re ≤ 2) :
    ‖dottieRangePolynomial S s‖ ≤ 2*10^13*10^49 := by
  have hB := archivedThetaScale_pos
  unfold dottieRangePolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)| * (10^49 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn₀ : 0 < n := (hS n hn).1
      have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
      have hn₁ : (n : ℝ) ≤ 10^13 := by exact_mod_cast (hS n hn).2
      have hb : 0 < archivedThetaScale/(n : ℝ) := div_pos hB hn'
      rw [norm_mul, Complex.norm_intCast, norm_cpow_eq_rpow_re_of_pos hb]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rcases le_total (archivedThetaScale/(n : ℝ)) 1 with hb₁ | hb₁
      · refine (Real.rpow_le_rpow_of_exponent_ge hb hb₁ hr).trans ?_
        have hs : (archivedThetaScale/(n : ℝ))^(-7 : ℝ) = ((n : ℝ)/archivedThetaScale)^7 := by
          rw [Real.rpow_neg hb.le, Real.div_rpow hB.le hn'.le, inv_div, div_pow]
          simp only [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hs]
        have hc : (n : ℝ)/archivedThetaScale ≤ 10^7 := by
          apply (div_le_iff₀ hB).mpr
          linarith only [hn₁, dottie_theta_scale_gt_three_halves_million]
        exact (pow_le_pow_left₀ (by positivity) hc 7).trans (by norm_num)
      · refine (Real.rpow_le_rpow_of_exponent_le hb₁ hr').trans ?_
        rw [Real.rpow_two]
        have hn₂ : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
        have hc : archivedThetaScale/(n : ℝ) ≤ 2*10^6 :=
          (div_le_self hB.le hn₂).trans dottie_theta_scale_lt_two_million.le
        exact (pow_le_pow_left₀ hb.le hc 2).trans (by norm_num)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      have hm : (∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)|) ≤ (2*10^13 : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          dottie_finite_absolute_mass_le S (L := 10^13) hS
      exact mul_le_mul_of_nonneg_right hm (by norm_num)

private theorem lower_horizontal_exp_small : Real.exp (-351 : ℝ) ≤ 1/10^149 := by
  have he : (8/3 : ℝ)^351 ≤ Real.exp 351 := by
    rw [show (351 : ℝ) = (351 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 351
  have hpow : (10 : ℕ)^149*3^351 ≤ 8^351 := by decide +kernel
  have hr : (10 : ℝ)^149 ≤ (8/3)^351 := by
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast hpow)
  have hp : (10 : ℝ)^149 ≤ Real.exp 351 := hr.trans he
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos _) (show (0 : ℝ) < 10^149 by positivity)).mpr hp

theorem dottie_normalized_lower_horizontal_bound (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13)
    {w : ℂ} (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) {h : ℝ} (hh : |h| = 20) :
    ‖dottieLowerHorizontalEdge S w h /
      (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))‖ ≤
        1/10^39 := by
  let B := archivedThetaScale
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  let den : ℂ := 2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)
  let M : ℝ := (2*10^13*10^49)*(4*10^35)*(1/10^149)
  have hB : 1 ≤ B := by linarith only [dottie_theta_scale_gt_three_halves_million]
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hden : ‖den‖ = 2*Real.pi*(B^2*G) := by
    unfold den
    have he : (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)) =
        ((2*Real.pi*(B^2*G) : ℝ) : ℂ) := by
      rw [show archivedDottieCompletionScale = B^2*G from rfl]
      push_cast
      rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc (-7 : ℝ) 1) :
      ‖dottieRightIntegrand S w (horizontalPoint h x)/den‖ ≤ M := by
    let z := horizontalPoint h x
    have hzr : z.re = x := by simp [z, horizontalPoint]
    have hzi : z.im = h := by simp [z, horizontalPoint]
    have hnormz : 20 ≤ ‖z‖ := by simpa only [hzi, hh] using Complex.abs_im_le_norm z
    have hd : (1 : ℝ) ≤ ‖z‖*(2*Real.pi*B^2) := by
      have hB₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hB 2
      have hπ : 1 ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
      have hp := mul_le_mul hπ hB₂ (by norm_num) (by positivity : 0 ≤ 2*Real.pi)
      exact (mul_le_mul (show (1 : ℝ) ≤ ‖z‖ by linarith only [hnormz]) hp
        (by norm_num : (0 : ℝ) ≤ 1*1^2) (norm_nonneg _)).trans' (by norm_num)
    have hs : w+z = ⟨w.re+x,w.im+h⟩ := by apply Complex.ext <;> simp [hzr,hzi]
    have hp := lower_horizontal_power_mass_le S hS (s := w+z)
      (by rw [hs]; change -7 ≤ w.re+x; linarith only [hr.1,hx.1])
      (by rw [hs]; change w.re+x ≤ 2; linarith only [hr.2,hx.2])
    have hg : ‖Gamma (w+z)‖ * Real.exp (Real.pi*h/2)/G ≤ 4*10^35 := by
      rw [hs]
      exact dottie_lower_gamma_horizontal hr hi hx (hh.le)
    have hexp :
        ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ =
          Real.exp (x^2-h^2)*Real.exp (Real.pi*h/2) := by
      have he : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
        ring
      rw [Complex.norm_exp, he, hzr, hzi, Real.exp_add]
    have hex : Real.exp (x^2-h^2) ≤ 1/10^149 := by
      have hx' : |x| ≤ 7 := abs_le.mpr ⟨hx.1, by linarith only [hx.2]⟩
      have hx₂ := pow_le_pow_left₀ (abs_nonneg x) hx' 2
      rw [sq_abs] at hx₂
      have hh₂ : h^2 = 400 := by rw [← sq_abs h, hh]; norm_num
      exact (Real.exp_le_exp.mpr (by linarith only [hx₂,hh₂] : x^2-h^2 ≤ -351)).trans
        lower_horizontal_exp_small
    change ‖dottieRightIntegrand S w z/den‖ ≤ _
    rw [dottieRightIntegrand, norm_div, norm_div, norm_mul, norm_mul, hexp, hden]
    calc
      _ = ‖dottieRangePolynomial S (w+z)‖ * (‖Gamma (w+z)‖*Real.exp (Real.pi*h/2)/G) *
        Real.exp (x^2-h^2)/(‖z‖*(2*Real.pi*B^2)) := by ring
      _ ≤ M/1 := by
        apply div_le_div₀ (by dsimp [M]; positivity) ?_ (by norm_num) hd
        dsimp only [M]
        gcongr
      _ = M := div_one _
  change ‖dottieLowerHorizontalEdge S w h / den‖ ≤ _
  rw [dottieLowerHorizontalEdge, ← intervalIntegral.integral_div]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-7 : ℝ)) (b := 1) (C := M)
    (f := fun x => dottieRightIntegrand S w (horizontalPoint h x)/den) (fun x hx => by
      rw [uIoc_of_le (by norm_num : (-7 : ℝ) ≤ 1)] at hx
      exact hpoint x ⟨hx.1.le,hx.2⟩)
  refine hb.trans ?_
  dsimp [M]
  norm_num

#print axioms dottie_normalized_lower_horizontal_bound

end QuarticModel
