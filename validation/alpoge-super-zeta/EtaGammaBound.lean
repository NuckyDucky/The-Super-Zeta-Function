import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds

/-! Gamma estimates for normalizing the finite eta expansion. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.EtaMellin

open Complex MeasureTheory Set

theorem gamma_real_le_four {x : ℝ} (hlo : 1/4 ≤ x) (hhi : x ≤ 1) :
    Real.Gamma x ≤ 4 := by
  have hx : 0 < x := by linarith
  have ht : Real.Gamma 2 = 1 := by
    rw [show (2:ℝ) = 1+1 by norm_num, Real.Gamma_add_one one_ne_zero,
      Real.Gamma_one, one_mul]
  have hC := Real.convexOn_Gamma.2
  have hCv := hC (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Ioi 0 by norm_num)
    (a := 1-x) (b := x) (by linarith) hx.le (by ring)
  have hadd : 1-x+x*2 = x+1 := by ring
  simp only [smul_eq_mul, Real.Gamma_one, ht, mul_one, sub_add_cancel] at hCv
  rw [hadd, Real.Gamma_add_one hx.ne'] at hCv
  have hlow := mul_le_mul_of_nonneg_right hlo (Real.Gamma_pos_of_pos hx).le
  linarith only [hlow, hCv]

theorem gamma_norm_le_gamma_real {w : ℂ} (h : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral h, Complex.GammaIntegral, Real.Gamma_eq_integral h]
  refine norm_integral_le_of_norm_le (Real.GammaIntegral_convergent h) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hx), sub_re, one_re]

private theorem sine_norm_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  refine (norm_sub_le ..).trans ?_
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, neg_neg]
  linarith only [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]

theorem gamma_inv_norm_le {w : ℂ} (hlo : 1/4 ≤ w.re) (hhi : w.re ≤ 3/4) :
    ‖Complex.Gamma w‖⁻¹ ≤ 4 * Real.exp (Real.pi * |w.im|) := by
  have hr : 0 < w.re := by linarith
  have hs : 1/4 ≤ (1-w).re ∧ (1-w).re ≤ 1 := by
    simp only [sub_re, one_re]
    exact ⟨by linarith, by linarith⟩
  have hs0 : 0 < (1-w).re := by linarith only [hs.1]
  have hg0 := Complex.Gamma_ne_zero_of_re_pos hr
  have hh0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hReflection := Complex.Gamma_mul_Gamma_one_sub w
  let z := (Real.pi:ℂ) * w
  have hnz : Complex.sin z ≠ 0 := by
    intro he
    change Complex.Gamma w * Complex.Gamma (1-w) = (Real.pi:ℂ) / Complex.sin z at hReflection
    rw [he, div_zero] at hReflection
    exact mul_ne_zero hg0 hh0 hReflection
  have heq := congrArg norm hReflection
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at heq
  change ‖Complex.Gamma w‖ * ‖Complex.Gamma (1-w)‖ = Real.pi / ‖Complex.sin z‖ at heq
  have h : ‖Complex.Gamma w‖⁻¹ =
      ‖Complex.Gamma (1-w)‖ * ‖Complex.sin z‖ / Real.pi := by
    rw [eq_div_iff (ne_of_gt Real.pi_pos), mul_comm, ← div_eq_mul_inv]
    apply (div_eq_iff (norm_ne_zero_iff.mpr hg0)).mpr
    have h := (eq_div_iff (norm_ne_zero_iff.mpr hnz)).mp heq
    linear_combination -h
  have hG := (gamma_norm_le_gamma_real hs0).trans (gamma_real_le_four hs.1 hs.2)
  have hsin : ‖Complex.sin z‖ ≤ Real.exp (Real.pi * |w.im|) := by
    simpa only [z, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul,
      abs_of_pos Real.pi_pos] using sine_norm_le z
  have hpi : (1:ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
  rw [h]
  exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpi).trans
    (mul_le_mul hG hsin (norm_nonneg _) (by norm_num))

#print axioms gamma_real_le_four
#print axioms gamma_inv_norm_le

end DottieOriented.NativeSpectrum.EtaMellin
end
