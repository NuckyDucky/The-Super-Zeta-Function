import WeightedContourTaylor

namespace FieldTarget

open MeasureTheory Metric Set
open scoped Interval NNReal

noncomputable section

private theorem integral_abs_power_on_panel (c h : ℝ) (n : ℕ) (hh : 0 ≤ h) :
    (∫ x in c - h..c + h, |x - c| ^ n) = 2 * h ^ (n + 1) / (n + 1) := by
  have hl : c - h ≤ c := by linarith only [hh]
  have hr : c ≤ c + h := by linarith only [hh]
  have hL := integral_pow_abs_sub_uIoc (a := c) (b := c - h) (n := n)
  have hR := integral_pow_abs_sub_uIoc (a := c) (b := c + h) (n := n)
  rw [uIoc_of_ge hl, ← intervalIntegral.integral_of_le hl,
    show c - h - c = -h by ring, abs_neg, abs_of_nonneg hh] at hL
  rw [uIoc_of_le hr, ← intervalIntegral.integral_of_le hr,
    show c + h - c = h by ring, abs_of_nonneg hh] at hR
  have hc : Continuous (fun x : ℝ ↦ |x - c| ^ n) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (c - h) c)
    (hc.intervalIntegrable c (c + h)), hL, hR]
  ring

theorem norm_weightedPowerMoment_le {W : ℝ → ℂ} {c h B : ℝ} (n : ℕ)
    (hh : 0 ≤ h) (hW : Continuous W)
    (hB : ∀ x ∈ Icc (c - h) (c + h), ‖W x‖ ≤ B) :
    ‖∫ x in c - h..c + h, W x * ((x - c : ℝ) : ℂ) ^ n‖ ≤ 2 * B * h ^ (n + 1) / (n + 1) := by
  have hab : c - h ≤ c + h := by linarith only [hh]
  have hc : Continuous (fun x : ℝ ↦ W x * ((x - c : ℝ) : ℂ) ^ n) := hW.mul (by fun_prop)
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  calc
    _ ≤ ∫ x in c - h..c + h, B * |x - c| ^ n := by
      refine intervalIntegral.integral_mono_on hab (hc.norm.intervalIntegrable _ _)
        ((show Continuous (fun x : ℝ ↦ B * |x - c| ^ n) from by fun_prop).intervalIntegrable _ _) ?_
      intro x hx
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x hx) (by positivity)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_abs_power_on_panel c h n hh]
      ring

/-- Coefficient errors can be certified once for every weight with the same norm bound. -/
theorem weightedContourTaylorPanel_error_le_of_enclosures
    {F : ℂ → ℂ} {W : ℝ → ℂ} {c h M B : ℝ} {R : ℝ≥0} (n : ℕ)
    (a : ℕ → ℂ) (e : ℕ → ℝ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hF : Differentiable ℂ F)
    (hM : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) (hW : Continuous W)
    (hB₀ : 0 ≤ B) (hB : ∀ x ∈ Icc (c - h) (c + h), ‖W x‖ ≤ B)
    (ha : ∀ k ∈ Finset.range n, ‖contourTaylorCoeff F (c : ℂ) R k - a k‖ ≤ e k) :
    ‖(∫ x in c - h..c + h, W x * F (x : ℂ)) -
      ∑ k ∈ Finset.range n, a k * (∫ x in c - h..c + h, W x * ((x - c : ℝ) : ℂ) ^ k)‖ ≤
      2 * h * B * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) +
        2 * B * ∑ k ∈ Finset.range n, e k * h ^ (k + 1) / (k + 1) := by
  refine (norm_sub_le_norm_sub_add_norm_sub _ (weightedContourTaylorPanel F W c h R n) _).trans
    (add_le_add (weightedContourTaylorPanel_error_le n hh hr hF hM hW hB₀ hB) ?_)
  rw [weightedContourTaylorPanel, ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [← sub_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  rw [norm_mul]
  refine (mul_le_mul (ha k hk) (norm_weightedPowerMoment_le k hh hW hB)
    (norm_nonneg _) ((norm_nonneg _).trans (ha k hk))).trans_eq ?_
  ring

end

#print axioms norm_weightedPowerMoment_le
#print axioms weightedContourTaylorPanel_error_le_of_enclosures

end FieldTarget
