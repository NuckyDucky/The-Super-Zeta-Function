import DedekindDiscriminant23HigherPanel
import DedekindDiscriminant23ReadingCover
import DedekindDiscriminant23CoefficientData
import MellinFixedTaylorTail

/-! Use the original sample boxes with their individual exponential radii. -/

namespace FieldTarget

open Complex Set
open DottieOriented.NativeSpectrum.MellinFixed
open scoped BigOperators

noncomputable section

def discriminant23EightTerms : ℕ := 54

private def amplitudeMass (odd : Bool) (j : ℕ) : ℤ :=
  ComplexBox.coefficientMass (ComplexBox.real (discriminant23StoredReadingAmplitudeBox odd j))

private def integerMomentMass (odd : Bool) : ℤ :=
  ∑ j ∈ Finset.range 257, amplitudeMass odd j * (j : ℤ) ^ 72

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
private theorem integerMomentMass_le (odd : Bool) :
    integerMomentMass odd ≤ (60000000000000 : ℤ) * (256 : ℤ) ^ 72 := by
  cases odd <;> decide +kernel

theorem discriminant23_readingMomentMass_le (odd : Bool) :
    discriminant23ReadingMomentMass odd ≤ 6 / 10 ^ 11 := by
  let D : ℝ := (scale : ℝ) * (256 : ℝ) ^ 72
  have hD : 0 < D := mul_pos scale_pos (by positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range 257, ((amplitudeMass odd j * (j : ℤ) ^ 72 : ℤ) : ℝ) / D := by
      unfold discriminant23ReadingMomentMass
      apply Finset.sum_le_sum
      intro j hj
      have hBox := ComplexBox.norm_le_coefficientMass
        (ComplexBox.real_contains (discriminant23_storedAmplitudeBox_contains odd
          (Finset.mem_range.mp hj)))
      have hAmp : |discriminant23ReadingAmplitude odd j| ≤
          (amplitudeMass odd j : ℝ) / (scale : ℝ) := by
        simpa only [amplitudeMass, Complex.norm_real, Real.norm_eq_abs] using hBox
      refine (mul_le_mul_of_nonneg_right hAmp (by positivity)).trans_eq ?_
      rw [discriminant23ReadingNode,
        show (3 * (j : ℝ) / 256) / 3 = (j : ℝ) / 256 by ring, div_pow]
      simp only [D, Int.cast_mul, Int.cast_pow, Int.cast_natCast, div_mul_div_comm]
    _ = (integerMomentMass odd : ℝ) / D := by
      rw [← Finset.sum_div, integerMomentMass, Int.cast_sum]
    _ ≤ ((60000000000000 * (256 : ℤ) ^ 72 : ℤ) : ℝ) / D := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast integerMomentMass_le odd) hD.le
    _ = _ := by norm_num [D, scale]

private theorem argument_radius_to_eight {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 8) : ‖discriminant23ReadingArgument w‖ ≤ 67 / 50 := by
  let z := discriminant23ReadingArgument w
  have hRe : |z.re| ≤ 1 / 12 := by
    rw [show z.re = (w.re - 1 / 2) / 6 from discriminant23_readingArgument_re w]
    exact abs_le.mpr ⟨by linarith only [hre.1], by linarith only [hre.2]⟩
  have hIm : |z.im| ≤ 4 / 3 := by
    rw [show z.im = w.im / 6 from discriminant23_readingArgument_im w, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    linarith only [him]
  have hReSq := pow_le_pow_left₀ (abs_nonneg _) hRe 2
  have hImSq := pow_le_pow_left₀ (abs_nonneg _) hIm 2
  rw [sq_abs] at hReSq hImSq
  have hsq : ‖z‖ ^ 2 ≤ (67 / 50 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [hReSq, hImSq]
  change ‖z‖ ≤ 67 / 50
  nlinarith only [hsq, norm_nonneg z]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem weighted_tail_at_eight (odd : Bool) :
    ComplexBox.weightedTailMass
      (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox odd k))
      67 50 discriminant23EightTerms 72 ≤ (3 : ℤ) * 10 ^ 17 * (50 : ℤ) ^ 72 := by
  cases odd <;> decide +kernel

private theorem reading_tail_to_eight (odd : Bool) {w : ℂ}
    (hz : ‖discriminant23ReadingArgument w‖ ≤ 67 / 50) :
    ‖discriminant23ReadingTaylor odd w -
      discriminant23ReadingTaylorUpTo odd discriminant23EightTerms w‖ ≤ 3 / 10 ^ 7 := by
  have h := ComplexBox.polynomial_tail_le_of_weighted_mass
    (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox odd k))
    (fun k ↦ (discriminant23ReadingCoefficient odd k : ℂ))
    (p := 67) (q := 50) (m := discriminant23EightTerms) (n := 72)
    (budget := 3 * 10 ^ 17) (by decide) (by decide)
    (by simpa only [Nat.cast_ofNat] using hz)
    (fun k _ ↦ ComplexBox.real_contains (discriminant23_storedReadingCoefficientBox_contains odd k))
    (weighted_tail_at_eight odd)
  have hUnit : ((3 * 10 ^ 17 : ℤ) : ℝ) / (scale : ℝ) = 3 / 10 ^ 7 := by norm_num [scale]
  rw [hUnit] at h
  exact h

/-- The value and slope bounds keep the same 257 integration nodes and the
same certified coefficient rows after enlarging the height allowance. -/
theorem discriminant23_reading_error_to_eight {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 8) :
    ‖discriminant23CharacterFold w - discriminant23ReadingTaylorUpTo false discriminant23EightTerms w‖
        ≤ 14 / 10 ^ 6 ∧
    ‖deriv discriminant23CharacterFold w -
        discriminant23ReadingTaylorUpTo true discriminant23EightTerms w‖ ≤ 14 / 10 ^ 6 := by
  have hz := argument_radius_to_eight hre him
  have hQuad := discriminant23_character_quadrature_bounds_to_eight hre.1 hre.2 him
  have hTaylor := discriminant23_character_taylor_bounds_of_quadrature_weighted hre.1 hre.2
    (r := 67 / 50) (by norm_num) hz hQuad.1 hQuad.2
  have hSmall (odd : Bool) :
      discriminant23ReadingMomentMass odd *
        (4 * (18 * (67 / 50 : ℝ)) ^ 72 / (Nat.factorial 72 : ℝ)) ≤ 1 / 10 ^ 9 := by
    refine (mul_le_mul_of_nonneg_right (discriminant23_readingMomentMass_le odd)
      (by positivity)).trans ?_
    norm_num [Nat.factorial]
  have hValueModel := discriminant23_characterComplexModel_error (w := w)
    (by linarith only [hre.1]) (by linarith only [hre.2])
  have hSlopeModel := discriminant23_characterComplexModel_iteratedDeriv_error 1 hre.1 hre.2
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one] at hSlopeModel
  have hCombine (odd : Bool) (F model : ℂ) (hModel : ‖F - model‖ ≤ 1 / 100000)
      (hTaylor : ‖model - discriminant23ReadingTaylor odd w‖ ≤
        11 / 10 ^ 7 + (11 / 5000000 + discriminant23ReadingMomentMass odd *
          (4 * (18 * (67 / 50 : ℝ)) ^ 72 / (Nat.factorial 72 : ℝ)))) :
      ‖F - discriminant23ReadingTaylorUpTo odd discriminant23EightTerms w‖ ≤ 14 / 10 ^ 6 := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ model _).trans ?_
    have hLast := (norm_sub_le_norm_sub_add_norm_sub _ (discriminant23ReadingTaylor odd w) _).trans
      (add_le_add hTaylor (reading_tail_to_eight odd hz))
    linarith only [hModel, hLast, hSmall odd]
  exact ⟨hCombine false _ _ hValueModel hTaylor.1, hCombine true _ _ hSlopeModel hTaylor.2⟩

#print axioms integerMomentMass_le
#print axioms discriminant23_readingMomentMass_le
#print axioms weighted_tail_at_eight
#print axioms discriminant23_reading_error_to_eight

end
end FieldTarget
