import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma

/-! Extend the exponential Gamma bound across any fixed positive strip.
The constants here may depend on the width of the strip. -/

namespace AlpogeSuperZeta

open Complex

noncomputable section

theorem gaussianGamma_fixed_positive_strip (n : ℕ) :
    ∃ B ≥ 0, ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 11 / 2 + (n : ℝ) →
      ‖Gamma z‖ ≤ B * (1 + |z.im|) ^ (n + 5) * Real.exp (-(Real.pi / 2 * |z.im|)) := by
  induction n with
  | zero =>
    refine ⟨3 * (7 : ℝ) ^ (5 : ℕ), by positivity, fun z hz₁ hz₂ => ?_⟩
    simp only [Nat.cast_zero, add_zero] at hz₂
    have h := PI.EF.Gamma_decay hz₁ hz₂
    have hNorm : ‖z + 1‖ ≤ 7 * (1 + |z.im|) := by
      refine (Complex.norm_le_abs_re_add_abs_im (z + 1)).trans ?_
      rw [add_re, one_re, add_im, one_im, add_zero, abs_of_nonneg (by linarith)]
      linarith [abs_nonneg z.im]
    have hB := pow_le_pow_left₀ (norm_nonneg (z + 1)) hNorm (5 : ℕ)
    rw [mul_pow] at hB
    simp only [zero_add]
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith
  | succ n ih =>
    obtain ⟨B, hB, h⟩ := ih
    refine ⟨((n : ℝ) + 7) * B, by positivity, fun z hz₁ hz₂ => ?_⟩
    let T := 1 + |z.im|
    have hT : 1 ≤ T := le_add_of_nonneg_right (abs_nonneg _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h7 : (1 : ℝ) ≤ (n : ℝ) + 7 := by linarith
    by_cases hz : z.re ≤ 11 / 2 + (n : ℝ)
    · refine (h z hz₁ hz).trans ?_
      have hpow : T ^ (n + 5) ≤ T ^ (n.succ + 5) :=
        pow_le_pow_right₀ hT (by omega)
      have hB' : B ≤ ((n : ℝ) + 7) * B := le_mul_of_one_le_left hB h7
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hB' hpow (by positivity) (by positivity)) (Real.exp_pos _).le
    let u := z - 1
    have hu₁ : 1 / 2 ≤ u.re := by
      change 1 / 2 ≤ (z - 1).re
      rw [sub_re, one_re]
      linarith
    have hu₂ : u.re ≤ 11 / 2 + (n : ℝ) := by
      change (z - 1).re ≤ 11 / 2 + (n : ℝ)
      rw [Nat.cast_succ] at hz₂
      rw [sub_re, one_re]
      linarith
    have huIm : u.im = z.im := by simp [u, sub_im]
    have hu₀ : u ≠ 0 := by
      intro he
      simp only [he, zero_re] at hu₁
      norm_num at hu₁
    have hNorm : ‖u‖ ≤ ((n : ℝ) + 7) * T := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [abs_of_nonneg (by linarith : 0 ≤ u.re), huIm]
      dsimp only [T]
      nlinarith [mul_nonneg (sub_nonneg.mpr h7) (abs_nonneg z.im)]
    have hRec : Gamma z = u * Gamma u := by
      rw [show z = u + 1 by simp [u], Gamma_add_one u hu₀]
    have hu := h u hu₁ hu₂
    rw [huIm] at hu
    rw [hRec, norm_mul]
    calc
      _ ≤ (((n : ℝ) + 7) * T) *
          (B * T ^ (n + 5) * Real.exp (-(Real.pi / 2 * |z.im|))) :=
        mul_le_mul hNorm hu (norm_nonneg _) (by positivity)
      _ = _ := by
        change _ = (((n : ℝ) + 7) * B) * T ^ (n.succ + 5) * _
        rw [show n.succ + 5 = (n + 5) + 1 by omega, pow_succ T (n + 5)]
        ring

#print axioms gaussianGamma_fixed_positive_strip

end
end AlpogeSuperZeta
