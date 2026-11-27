import DedekindDiscriminant23ReadingCells
import DedekindDiscriminant23CoefficientData
import Mathlib.Algebra.BigOperators.Intervals

/-! The checked coefficient boxes also bound the discarded Taylor terms. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed
open scoped BigOperators

noncomputable section

private def boxMass (b : Box) : ℤ := max |b.lo| |b.hi|

private theorem norm_le_boxMass {b : Box} {a : ℝ} (h : Contains b a) :
    ‖(a : ℂ)‖ ≤ (boxMass b : ℝ) / (scale : ℝ) := by
  have ha : |(scale : ℝ) * a| ≤ (boxMass b : ℝ) := by
    apply abs_le.mpr
    simp only [boxMass, Int.cast_max, Int.cast_abs]
    exact ⟨(neg_le_neg (le_max_left |(b.lo : ℝ)| |(b.hi : ℝ)|)).trans
      ((neg_abs_le (b.lo : ℝ)).trans h.1),
      h.2.trans ((le_abs_self (b.hi : ℝ)).trans (le_max_right _ _))⟩
  rw [Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ scale_pos, mul_comm |a|]
  simpa only [abs_mul, abs_of_pos scale_pos] using ha

private def tailMass (odd : Bool) : ℤ :=
  ∑ k ∈ Finset.Ico discriminant23ReadingTerms 72,
    boxMass (discriminant23StoredReadingCoefficientBox odd k)

private theorem tailMass_le (odd : Bool) : tailMass odd ≤ 40 * 10 ^ 18 := by
  cases odd <;> decide +kernel

/-- Both rows use the same uniform allowance on the normalized unit disk. -/
theorem discriminant23_reading_partial_error_le (odd : Bool) {w : ℂ}
    (hz : ‖discriminant23ReadingArgument w‖ ≤ 1) :
    ‖discriminant23ReadingTaylor odd w - discriminant23ReadingPartialTaylor odd w‖ ≤
      40 / 1000000 := by
  unfold discriminant23ReadingTaylor discriminant23ReadingPartialTaylor
  rw [← Finset.sum_Ico_eq_sub _ (show discriminant23ReadingTerms ≤ 72 by decide)]
  calc
    _ ≤ ∑ k ∈ Finset.Ico discriminant23ReadingTerms 72,
        ‖(discriminant23ReadingCoefficient odd k : ℂ) *
          discriminant23ReadingArgument w ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico discriminant23ReadingTerms 72,
        (boxMass (discriminant23StoredReadingCoefficientBox odd k) : ℝ) / (scale : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hz)).trans
        (norm_le_boxMass (discriminant23_storedReadingCoefficientBox_contains odd k))
    _ = (tailMass odd : ℝ) / (scale : ℝ) := by
      rw [← Finset.sum_div, tailMass, Int.cast_sum]
    _ ≤ (40 * 10 ^ 18 : ℝ) / (scale : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast tailMass_le odd) scale_pos.le
    _ = _ := by norm_num [scale]

#print axioms tailMass_le
#print axioms discriminant23_reading_partial_error_le

end

end FieldTarget
