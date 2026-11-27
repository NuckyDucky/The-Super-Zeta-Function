import DedekindDiscriminant23EightError

/-! Compare the 68-term reading with the actual completed character and its derivative. -/

namespace FieldTarget

open Complex Set
open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

private theorem argument_radius_to_nineteen_halves {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 19 / 2) : ‖discriminant23ReadingArgument w‖ ≤ 8 / 5 := by
  let z := discriminant23ReadingArgument w
  have hRe : |z.re| ≤ 1 / 12 := by
    rw [show z.re = (w.re - 1 / 2) / 6 from discriminant23_readingArgument_re w]
    exact abs_le.mpr ⟨by linarith only [hre.1], by linarith only [hre.2]⟩
  have hIm : |z.im| ≤ 19 / 12 := by
    rw [show z.im = w.im / 6 from discriminant23_readingArgument_im w, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    linarith only [him]
  have hReSq := pow_le_pow_left₀ (abs_nonneg _) hRe 2
  have hImSq := pow_le_pow_left₀ (abs_nonneg _) hIm 2
  rw [sq_abs] at hReSq hImSq
  have hsq : ‖z‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [hReSq, hImSq]
  change ‖z‖ ≤ 8 / 5
  nlinarith only [hsq, norm_nonneg z]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem weighted_tail_to_nineteen_halves (odd : Bool) :
    ComplexBox.weightedTailMass
      (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox odd k))
      8 5 68 72 ≤ (9 : ℤ) * 10 ^ 16 * (5 : ℤ) ^ 72 := by
  cases odd <;> decide +kernel

private theorem reading_tail_to_nineteen_halves (odd : Bool) {w : ℂ}
    (hz : ‖discriminant23ReadingArgument w‖ ≤ 8 / 5) :
    ‖discriminant23ReadingTaylor odd w - discriminant23ReadingTaylorUpTo odd 68 w‖ ≤ 9 / 10 ^ 8 := by
  have h := ComplexBox.polynomial_tail_le_of_weighted_mass
    (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox odd k))
    (fun k ↦ (discriminant23ReadingCoefficient odd k : ℂ))
    (p := 8) (q := 5) (m := 68) (n := 72)
    (budget := 9 * 10 ^ 16) (by decide) (by decide)
    (by simpa only [Nat.cast_ofNat] using hz)
    (fun k _ ↦ ComplexBox.real_contains (discriminant23_storedReadingCoefficientBox_contains odd k))
    (weighted_tail_to_nineteen_halves odd)
  have hUnit : ((9 * 10 ^ 16 : ℤ) : ℝ) / (scale : ℝ) = 9 / 10 ^ 8 := by norm_num [scale]
  rw [hUnit] at h
  exact h

theorem discriminant23_reading_error_to_nineteen_halves {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 19 / 2) :
    ‖discriminant23CharacterFold w - discriminant23ReadingTaylorUpTo false 68 w‖ ≤ 45 / 10 ^ 8 ∧
    ‖deriv discriminant23CharacterFold w - discriminant23ReadingTaylorUpTo true 68 w‖ ≤ 11 / 10 ^ 7 := by
  have hz := argument_radius_to_nineteen_halves hre him
  have hQuad := discriminant23_character_quadrature_bounds_to_nineteen_halves hre.1 hre.2 him
  have hTaylor := discriminant23_character_taylor_bounds_of_quadrature_sharp hre.1 hre.2
    (r := 8 / 5) (by norm_num) hz hQuad.1 hQuad.2
  have hSmall (odd : Bool) :
      discriminant23ReadingMomentMass odd *
        (4 * (18 * (8 / 5 : ℝ)) ^ 72 / (Nat.factorial 72 : ℝ)) ≤ 1 / 10 ^ 8 := by
    refine (mul_le_mul_of_nonneg_right (discriminant23_readingMomentMass_le odd)
      (by positivity)).trans ?_
    norm_num [Nat.factorial]
  have hValueModel := discriminant23_characterComplexModel_error_sharp (w := w)
    (by linarith only [hre.1]) (by linarith only [hre.2])
  have hSlopeModel := discriminant23_characterComplexModel_iteratedDeriv_error_sharp 1 hre.1 hre.2
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one] at hSlopeModel
  have hCombine (odd : Bool) (F model : ℂ) (E : ℝ) (hm : ‖F - model‖ ≤ 1 / 10 ^ 9)
      (ht : ‖model - discriminant23ReadingTaylor odd w‖ ≤
        E + (1 / 10 ^ 7 + discriminant23ReadingMomentMass odd *
          (4 * (18 * (8 / 5 : ℝ)) ^ 72 / (Nat.factorial 72 : ℝ)))) :
      ‖F - discriminant23ReadingTaylorUpTo odd 68 w‖ ≤ E + 21 / 10 ^ 8 := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ model _).trans ?_
    have hLast := (norm_sub_le_norm_sub_add_norm_sub _ (discriminant23ReadingTaylor odd w) _).trans
      (add_le_add ht (reading_tail_to_nineteen_halves odd hz))
    linarith only [hm, hLast, hSmall odd]
  exact ⟨(hCombine false _ _ _ hValueModel hTaylor.1).trans (by norm_num),
    (hCombine true _ _ _ hSlopeModel hTaylor.2).trans (by norm_num)⟩

end

#print axioms weighted_tail_to_nineteen_halves
#print axioms discriminant23_reading_error_to_nineteen_halves

end FieldTarget
