import DedekindDiscriminant23NineteenHalvesError

namespace FieldTarget

open Complex Set

/-- Exact full-strip height range of the radius used in the 68-term estimate. -/
theorem discriminant23_taylor_radius_eight_fifths_iff (T : ℝ) (hT : 0 ≤ T) :
    (∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → |w.im| ≤ T →
      ‖discriminant23ReadingArgument w‖ ≤ 8 / 5) ↔ T ^ 2 ≤ 9191 / 100 := by
  constructor
  · intro h
    let w : ℂ := ⟨1, T⟩
    have hRadius := h w (by norm_num [w]) (by simp [w, abs_of_nonneg hT])
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hRadius 2
    rw [Complex.sq_norm, Complex.normSq_apply, discriminant23_readingArgument_re,
      discriminant23_readingArgument_im] at hSq
    change ((1 - 1 / 2) / 6) * ((1 - 1 / 2) / 6) + (T / 6) * (T / 6) ≤
      (8 / 5 : ℝ) ^ 2 at hSq
    nlinarith only [hSq]
  · intro hLimit w hre him
    let z := discriminant23ReadingArgument w
    have hRe : |z.re| ≤ 1 / 12 := by
      rw [show z.re = (w.re - 1 / 2) / 6 from discriminant23_readingArgument_re w]
      exact abs_le.mpr ⟨by linarith only [hre.1], by linarith only [hre.2]⟩
    have hIm : |z.im| ≤ T / 6 := by
      rw [show z.im = w.im / 6 from discriminant23_readingArgument_im w, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      exact div_le_div_of_nonneg_right him (by norm_num)
    have hReSq := pow_le_pow_left₀ (abs_nonneg _) hRe 2
    have hImSq := pow_le_pow_left₀ (abs_nonneg _) hIm 2
    rw [sq_abs] at hReSq hImSq
    have hSq : ‖z‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith only [hReSq, hImSq, hLimit]
    change ‖z‖ ≤ 8 / 5
    nlinarith only [hSq, norm_nonneg z]

#check discriminant23_taylor_radius_eight_fifths_iff
#print axioms discriminant23_taylor_radius_eight_fifths_iff

end FieldTarget
