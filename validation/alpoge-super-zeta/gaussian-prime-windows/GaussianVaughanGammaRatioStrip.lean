import GaussianVaughanGammaFixedStrip

/-! The exponential factors cancel from the reflected Gamma quotient.
This controls the Gaussian factor across the negative strips. -/

namespace AlpogeSuperZeta

open Complex

noncomputable section

private theorem norm_sine_le_exp_height (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, norm_ofNat]
  have h₁ : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simpa [mul_re] using Real.exp_le_exp.mpr (le_abs_self z.im)
  have h₂ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simpa [mul_re] using Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith [norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))]

private theorem gaussianGamma_ratio_norm_le {z : ℂ} (hz : z.re < 1) :
    ‖Gamma (1 - z) / Gamma z‖ ≤ ‖Gamma (1 - z)‖ ^ 2 * Real.exp (Real.pi * |z.im|) /
      Real.pi := by
  by_cases hzero : Gamma z = 0
  · rw [hzero, div_zero, norm_zero]
    positivity [Real.pi_pos]
  have hG : Gamma (1 - z) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [sub_re]; linarith)
  have he := Gamma_mul_Gamma_one_sub z
  let π : ℂ := Real.pi
  have hπ : π ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let s := Complex.sin (π * z)
  change Gamma z * Gamma (1 - z) = π / s at he
  have hs : s ≠ 0 := by
    intro h
    rw [h, div_zero] at he
    exact mul_ne_zero hzero hG he
  have hrefl : Gamma (1 - z) / Gamma z = Gamma (1 - z) ^ 2 * s / π := by
    have hh := (eq_div_iff hs).mp he
    apply (div_eq_div_iff hzero hπ).mpr
    calc
      _ = Gamma (1 - z) * (Gamma z * Gamma (1 - z) * s) := by rw [hh]
      _ = _ := by ring
  have hS : ‖s‖ ≤ Real.exp (Real.pi * |z.im|) := by
    have e : |(π * z).im| = Real.pi * |z.im| := by
      simp [π, mul_im, abs_mul, abs_of_pos Real.pi_pos]
    exact (norm_sine_le_exp_height (π * z)).trans_eq (congrArg Real.exp e)
  rw [hrefl, norm_div, norm_mul, norm_pow,
    show ‖π‖ = Real.pi by simp [π, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) Real.pi_pos.le

theorem gaussianGamma_ratio_norm_on_negative_strip (n : ℕ) :
    ∃ B ≥ 0, ∀ z : ℂ, -(n : ℝ) ≤ z.re → z.re ≤ -1 →
      ‖Gamma (1 - z) / Gamma z‖ ≤ B * (1 + |z.im|) ^ (2 * (n + 5)) := by
  obtain ⟨D, hD, hΓ⟩ := gaussianGamma_fixed_positive_strip n
  refine ⟨D ^ 2 / Real.pi, by positivity [Real.pi_pos], fun z hl hr => ?_⟩
  let w := 1 - z
  have h₁ : 1 / 2 ≤ w.re := by change 1 / 2 ≤ (1 - z).re; rw [sub_re, one_re]; linarith
  have h₂ : w.re ≤ 11 / 2 + (n : ℝ) := by
    change (1 - z).re ≤ _
    rw [sub_re, one_re]
    linarith
  have him : |w.im| = |z.im| := by
    change |(1 - z).im| = _
    rw [sub_im, one_im, zero_sub, abs_neg]
  have h := hΓ w h₁ h₂
  rw [him] at h
  have he : (Real.exp (-(Real.pi / 2 * |z.im|))) ^ (2 : ℕ) *
      Real.exp (Real.pi * |z.im|) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add,
      show ((2 : ℕ) : ℝ) * -(Real.pi / 2 * |z.im|) + Real.pi * |z.im| = 0 by push_cast; ring,
      Real.exp_zero]
  let T := 1 + |z.im|
  refine (gaussianGamma_ratio_norm_le (by linarith : z.re < 1)).trans ?_
  change ‖Gamma w‖ ^ 2 * Real.exp (Real.pi * |z.im|) / Real.pi ≤ _
  calc
    _ ≤ (D * T ^ (n + 5) * Real.exp (-(Real.pi / 2 * |z.im|))) ^ (2 : ℕ) *
        Real.exp (Real.pi * |z.im|) / Real.pi := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) h _) (Real.exp_pos _).le) Real.pi_pos.le
    _ = (D ^ (2 : ℕ) * (T ^ (n + 5)) ^ (2 : ℕ) *
        ((Real.exp (-(Real.pi / 2 * |z.im|))) ^ (2 : ℕ) * Real.exp (Real.pi * |z.im|))) /
        Real.pi := by rw [mul_pow, mul_pow]; ring
    _ = _ := by rw [he, mul_one, ← pow_mul, mul_comm (n + 5) (2 : ℕ)]; ring

#print axioms gaussianGamma_ratio_norm_on_negative_strip

end
end AlpogeSuperZeta
