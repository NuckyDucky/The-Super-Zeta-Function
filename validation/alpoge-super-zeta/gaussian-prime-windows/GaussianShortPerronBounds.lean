import GaussianShortPerron

/-! The short cutoff costs an arbitrarily small inverse power of its
width when used with an integrable vertical power. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

theorem one_add_abs_im_le_three_norm {z : ℂ} (h : 1 / 2 ≤ z.re) :
    1 + |z.im| ≤ 3 * ‖z‖ := by
  linarith [abs_im_le_norm z, abs_re_le_norm z, le_abs_self z.re]

private theorem shortPerronNumerator_small {z : ℂ} {d : ℝ}
    (hd : 0 < d) (hd₁ : d ≤ 1) (hR : z.re ≤ 3 / 2) (hz : z + 1 ≠ 0) :
    ‖(((1 + d : ℝ) : ℂ) ^ (z + 1)) - 1‖ ≤ (4 * d) * ‖z + 1‖ := by
  have hInt : ∫ t : ℝ in 1..(1 + d), (t : ℂ) ^ z =
      ((((1 + d : ℝ) : ℂ) ^ (z + 1)) - 1) / (z + 1) := by
    rw [integral_cpow (Or.inr ⟨fun e => hz (by rw [e]; norm_num), ?_⟩), ofReal_one, one_cpow]
    rw [uIcc_of_le (by linarith : (1 : ℝ) ≤ 1 + d)]
    simp
  have he : (((1 + d : ℝ) : ℂ) ^ (z + 1)) - 1 =
      (∫ t : ℝ in 1..(1 + d), (t : ℂ) ^ z) * (z + 1) := by
    rw [hInt, div_mul_cancel₀ _ hz]
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ 4 * |1 + d - 1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le (by linarith : (1 : ℝ) ≤ 1 + d)] at ht
      rw [norm_cpow_eq_rpow_re_of_pos (one_pos.trans ht.1)]
      calc
        _ ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
        _ ≤ 4 := by
          rw [Real.rpow_two]
          have h₀ : 0 ≤ 2 - t := by linarith [ht.2]
          have h₁ : 0 ≤ 2 + t := by linarith [ht.1]
          nlinarith [mul_nonneg h₀ h₁]
    _ = _ := by rw [add_sub_cancel_left, abs_of_pos hd]

private theorem shortPerronNumerator_large {z : ℂ} {d : ℝ}
    (hd : 0 < d) (hd₁ : d ≤ 1) (hR : z.re ≤ 3 / 2) :
    ‖(((1 + d : ℝ) : ℂ) ^ (z + 1)) - 1‖ ≤ 9 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < 1 + d), add_re, one_re]
  have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + d)
    (show z.re + 1 ≤ 3 by linarith)
  have h' := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + d)
    (by linarith : 1 + d ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)
  rw [show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num] at h'
  linarith [h.trans h']

theorem shortPerronMultiplier_two_bounds {z : ℂ} {d : ℝ}
    (hd : 0 < d) (hd₁ : d ≤ 1) (hL : 1 / 2 ≤ z.re) (hR : z.re ≤ 3 / 2) :
    ‖shortPerronMultiplier d z‖ ≤ 12 / (1 + |z.im|) ∧
    ‖shortPerronMultiplier d z‖ ≤ 81 / (d * (1 + |z.im|) ^ 2) := by
  let U := 1 + |z.im|
  have hU : 0 < U := by dsimp [U]; positivity
  have hZ : U ≤ 3 * ‖z‖ := one_add_abs_im_le_three_norm hL
  have hZ' : U ≤ 3 * ‖z + 1‖ := by
    have h : 1 / 2 ≤ (z + 1).re := by rw [add_re, one_re]; linarith
    simpa only [add_im, one_im, add_zero] using one_add_abs_im_le_three_norm h
  have hz : 0 < ‖z‖ := by linarith
  have hz' : 0 < ‖z + 1‖ := by linarith
  have hd₀ : 0 < d * ‖z‖ * ‖z + 1‖ := by positivity
  have hnorm : ‖shortPerronMultiplier d z‖ =
      ‖(((1 + d : ℝ) : ℂ) ^ (z + 1)) - 1‖ / (d * ‖z‖ * ‖z + 1‖) := by
    rw [shortPerronMultiplier, norm_div, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hd.le]
  constructor
  · rw [hnorm]
    calc
      _ ≤ (4 * d) * ‖z + 1‖ / (d * ‖z‖ * ‖z + 1‖) :=
        div_le_div_of_nonneg_right (shortPerronNumerator_small hd hd₁ hR (norm_pos_iff.mp hz')) hd₀.le
      _ = 4 / ‖z‖ := by field_simp
      _ ≤ 12 / U := (div_le_div_iff₀ hz hU).mpr (by linarith)
  · rw [hnorm]
    calc
      _ ≤ 9 / (d * ‖z‖ * ‖z + 1‖) :=
        div_le_div_of_nonneg_right (shortPerronNumerator_large hd hd₁ hR) hd₀.le
      _ ≤ 81 / (d * U ^ 2) := by
        have hm := mul_le_mul hZ hZ' hU.le (by positivity : 0 ≤ 3 * ‖z‖)
        apply (div_le_div_iff₀ hd₀ (by positivity)).mpr
        calc
          _ = 9 * d * (U * U) := by ring
          _ ≤ 9 * d * ((3 * ‖z‖) * (3 * ‖z + 1‖)) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
          _ = _ := by ring

theorem shortPerronMultiplier_norm_le {z : ℂ} {d e : ℝ}
    (hd : 0 < d) (hd₁ : d ≤ 1) (he : 0 < e) (he₁ : e ≤ 1)
    (hL : 1 / 2 ≤ z.re) (hR : z.re ≤ 3 / 2) :
    ‖shortPerronMultiplier d z‖ ≤ (81 * d ^ (-e)) / (1 + |z.im|) ^ (1 + e) := by
  let U := 1 + |z.im|
  have hU : 0 < U := by dsimp [U]; positivity
  let R := d * U
  have hR₀ : 0 < R := by dsimp [R]; positivity
  obtain ⟨hA, hB⟩ := shortPerronMultiplier_two_bounds hd hd₁ hL hR
  have heq : 81 * R ^ (-e) / U = (81 * d ^ (-e)) / U ^ (1 + e) := by
    rw [show R = d * U from rfl, Real.mul_rpow hd.le hU.le, Real.rpow_add hU, Real.rpow_one,
      Real.rpow_neg hU.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  change _ ≤ (81 * d ^ (-e)) / U ^ (1 + e)
  rw [← heq]
  by_cases h : 1 ≤ R
  · have hpow : R⁻¹ ≤ R ^ (-e) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h (by linarith)
    apply hB.trans
    have he' : 81 / (d * U ^ 2) = 81 * R⁻¹ / U := by
      dsimp [R]
      field_simp
    rw [he']
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hU.le
  · have hpow : 1 ≤ R ^ (-e) := by
      rw [← Real.rpow_zero R]
      exact Real.rpow_le_rpow_of_exponent_ge hR₀ (le_of_not_ge h) (by linarith)
    apply hA.trans
    exact div_le_div_of_nonneg_right (by linarith) hU.le

theorem one_add_log_le_power {T e : ℝ} (hT : 1 ≤ T) (he : 0 < e) :
    1 + Real.log T ≤ (1 + e⁻¹) * T ^ e := by
  have hT₀ := zero_lt_one.trans_le hT
  have hT₁ := Real.one_le_rpow hT he.le
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hT₀ e)
  rw [Real.log_rpow hT₀] at h
  have h' : Real.log T ≤ T ^ e / e := (le_div_iff₀ he).mpr (by nlinarith)
  rw [add_mul, one_mul, mul_comm e⁻¹, ← div_eq_mul_inv]
  linarith

#print axioms one_add_abs_im_le_three_norm
#print axioms shortPerronMultiplier_two_bounds
#print axioms shortPerronMultiplier_norm_le
#print axioms one_add_log_le_power

end
end AlpogeSuperZeta
