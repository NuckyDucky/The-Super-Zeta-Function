import DedekindDiscriminant23EightError
import DedekindDiscriminant23ReadingCover

/-! The signs used on the central crossing and both horizontal sides. -/

namespace FieldTarget

open Complex Set
open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

private def eightCellBox (odd : Bool) (k : ℕ) (l r : ℤ) : ComplexBox :=
  discriminant23ReadingCellBoxUpTo (discriminant23StoredReadingCoefficientBox odd)
    discriminant23EightTerms (2 * (k : ℤ) + 1) 1 96 l r 24

private def margin : ℤ := 16 * 10 ^ 18

private inductive Sign
  | rePositive
  | reNegative
  | imPositive
  | imNegative

private def Sign.read (s : Sign) (z : ℂ) : ℝ :=
  match s with
  | .rePositive => z.re
  | .reNegative => -z.re
  | .imPositive => z.im
  | .imNegative => -z.im

private def Sign.check (s : Sign) (b : ComplexBox) : Prop :=
  match s with
  | .rePositive => margin < b.re.lo
  | .reNegative => b.re.hi < -margin
  | .imPositive => margin < b.im.lo
  | .imNegative => b.im.hi < -margin

private instance (s : Sign) (b : ComplexBox) : Decidable (s.check b) := by
  cases s <;> unfold Sign.check <;> infer_instance

private theorem Sign.read_gt_of_check {s : Sign} {b : ComplexBox} {z : ℂ}
    (h : ComplexBox.Contains b z) (hcheck : s.check b) : 16 / 10 ^ 6 < s.read z := by
  have lower {B : Box} {x : ℝ} (hx : Contains B x) (hb : margin < B.lo) : 16 / 10 ^ 6 < x := by
    apply lt_of_box_lower hx
    rw [show (scale : ℝ) * (16 / 10 ^ 6) = (margin : ℝ) by norm_num [scale, margin]]
    exact_mod_cast hb
  have upper {B : Box} {x : ℝ} (hx : Contains B x) (hb : B.hi < -margin) : 16 / 10 ^ 6 < -x := by
    have ho : x < -(16 / 10 ^ 6) := by
      apply lt_of_box_upper hx
      rw [show (scale : ℝ) * (-(16 / 10 ^ 6)) = ((-margin : ℤ) : ℝ) by norm_num [scale, margin]]
      exact_mod_cast hb
    linarith only [ho]
  cases s
  · exact lower h.1 hcheck
  · exact upper h.1 hcheck
  · exact lower h.2 hcheck
  · exact upper h.2 hcheck

private theorem Sign.read_sub (s : Sign) (z q : ℂ) : s.read (z - q) = s.read z - s.read q := by
  cases s <;> simp only [Sign.read, Complex.sub_re, Complex.sub_im, neg_sub] <;> ring

private theorem Sign.abs_read_le_norm (s : Sign) (z : ℂ) : |s.read z| ≤ ‖z‖ := by
  cases s
  · exact Complex.abs_re_le_norm z
  · simpa only [Sign.read, abs_neg] using Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z
  · simpa only [Sign.read, abs_neg] using Complex.abs_im_le_norm z

private theorem eight_cell_contains (odd : Bool) {k : ℕ} {l r : ℤ} {w : ℂ}
    (hr : w.re ∈ Icc (1 / 2 + (l : ℝ) / 4) (1 / 2 + (r : ℝ) / 4))
    (ht : w.im ∈ Icc ((k : ℝ) / 8) (((k : ℝ) + 1) / 8)) :
    ComplexBox.Contains (eightCellBox odd k l r)
      (discriminant23ReadingTaylorUpTo odd discriminant23EightTerms w) := by
  have hRe := discriminant23_readingArgument_re w
  have hIm := discriminant23_readingArgument_im w
  apply discriminant23_readingCellBoxUpTo_contains _ odd _
    (discriminant23_storedReadingCoefficientBox_contains odd) (by norm_num) (by norm_num)
  · rw [hRe]
    linarith only [hr.1]
  · rw [hRe]
    linarith only [hr.2]
  · rw [hIm]
    push_cast
    linarith only [ht.1]
  · rw [hIm]
    push_cast
    linarith only [ht.2]

private theorem eight_sign_of_cells (sign : Sign) (odd : Bool) {start n : ℕ} {l r : ℤ} {w : ℂ}
    (hCheck : ∀ j : Fin (n + 1), sign.check (eightCellBox odd (start + j.val) l r))
    (hr : w.re ∈ Icc (1 / 2 + (l : ℝ) / 4) (1 / 2 + (r : ℝ) / 4))
    (ht : w.im ∈ Icc ((start : ℝ) / 8) (((start : ℝ) + n + 1) / 8))
    (hre : w.re ∈ Icc (0 : ℝ) 1) (him : |w.im| ≤ 8) :
    2 / 10 ^ 6 < sign.read (if odd then deriv discriminant23CharacterFold w else
      discriminant23CharacterFold w) := by
  obtain ⟨j, hj₀, hj₁⟩ := real_mem_equal_closed_cells ((start : ℝ) / 8) (1 / 8) w.im n ht.1
    (by push_cast; linarith only [ht.2])
  have hCell := eight_cell_contains odd hr (k := start + j.val) (w := w) (by
    push_cast
    exact ⟨by linarith only [hj₀], by linarith only [hj₁]⟩)
  have hRead := Sign.read_gt_of_check hCell (hCheck j)
  have hErr : ‖(if odd then deriv discriminant23CharacterFold w else
      discriminant23CharacterFold w) -
        discriminant23ReadingTaylorUpTo odd discriminant23EightTerms w‖ ≤ 14 / 10 ^ 6 := by
    cases odd
    · exact (discriminant23_reading_error_to_eight hre him).1
    · exact (discriminant23_reading_error_to_eight hre him).2
  have hδ := (abs_le.mp ((sign.abs_read_le_norm _).trans hErr)).1
  rw [sign.read_sub] at hδ
  linarith only [hRead, hδ]

set_option maxRecDepth 16384
set_option maxHeartbeats 24000000

private theorem below_checks (j : Fin 4) :
    Sign.reNegative.check (eightCellBox false (48 + j.val) (-2) 2) := by
  fin_cases j <;> decide +kernel

private theorem crossing_checks (j : Fin 7) :
    Sign.imNegative.check (eightCellBox true (52 + j.val) (-1) 1) := by
  fin_cases j <;> decide +kernel

private theorem left_checks (j : Fin 6) :
    Sign.imPositive.check (eightCellBox false (52 + j.val) (-2) (-1)) := by
  fin_cases j <;> decide +kernel

private theorem right_checks (j : Fin 6) :
    Sign.imNegative.check (eightCellBox false (52 + j.val) 1 2) := by
  fin_cases j <;> decide +kernel

private theorem left_positive_check (j : Fin 1) :
    Sign.rePositive.check (eightCellBox false (58 + j.val) (-2) (-1)) := by
  have hj : j.val = 0 := by omega
  rw [hj]
  decide +kernel

private theorem right_positive_check (j : Fin 1) :
    Sign.rePositive.check (eightCellBox false (58 + j.val) 1 2) := by
  have hj : j.val = 0 := by omega
  rw [hj]
  decide +kernel

private theorem above_left_checks (j : Fin 5) :
    Sign.rePositive.check (eightCellBox false (59 + j.val) (-2) 0) := by
  fin_cases j <;> decide +kernel

private theorem above_right_checks (j : Fin 5) :
    Sign.rePositive.check (eightCellBox false (59 + j.val) 0 2) := by
  fin_cases j <;> decide +kernel

theorem discriminant23_eight_below_negative {w : ℂ} (hr : w.re ∈ Icc (0 : ℝ) 1)
    (ht : w.im ∈ Icc (6 : ℝ) (13 / 2)) : (discriminant23CharacterFold w).re < -(2 / 10 ^ 6) := by
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have h := eight_sign_of_cells .reNegative false (n := 3) below_checks
    (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hr hAbs
  change 2 / 10 ^ 6 < -(discriminant23CharacterFold w).re at h
  linarith only [h]

theorem discriminant23_eight_crossing_slope_negative {w : ℂ}
    (hr : w.re ∈ Icc (1 / 4 : ℝ) (3 / 4)) (ht : w.im ∈ Icc (13 / 2 : ℝ) (59 / 8)) :
    (deriv discriminant23CharacterFold w).im < -(2 / 10 ^ 6) := by
  have hRe : w.re ∈ Icc (0 : ℝ) 1 := ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have h := eight_sign_of_cells .imNegative true (n := 6) crossing_checks
    (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hRe hAbs
  change 2 / 10 ^ 6 < -(deriv discriminant23CharacterFold w).im at h
  linarith only [h]

theorem discriminant23_eight_left_im_positive {w : ℂ} (hr : w.re ∈ Icc (0 : ℝ) (1 / 4))
    (ht : w.im ∈ Icc (13 / 2 : ℝ) (29 / 4)) : 2 / 10 ^ 6 < (discriminant23CharacterFold w).im := by
  have hRe : w.re ∈ Icc (0 : ℝ) 1 := ⟨hr.1, by linarith only [hr.2]⟩
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  exact eight_sign_of_cells .imPositive false (n := 5) left_checks
    (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hRe hAbs

theorem discriminant23_eight_right_im_negative {w : ℂ} (hr : w.re ∈ Icc (3 / 4 : ℝ) 1)
    (ht : w.im ∈ Icc (13 / 2 : ℝ) (29 / 4)) : (discriminant23CharacterFold w).im < -(2 / 10 ^ 6) := by
  have hRe : w.re ∈ Icc (0 : ℝ) 1 := ⟨by linarith only [hr.1], hr.2⟩
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have h := eight_sign_of_cells .imNegative false (n := 5) right_checks
    (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hRe hAbs
  change 2 / 10 ^ 6 < -(discriminant23CharacterFold w).im at h
  linarith only [h]

theorem discriminant23_eight_sides_re_positive {w : ℂ}
    (hr : w.re ∈ Icc (0 : ℝ) (1 / 4) ∨ w.re ∈ Icc (3 / 4 : ℝ) 1)
    (ht : w.im ∈ Icc (29 / 4 : ℝ) (59 / 8)) : 2 / 10 ^ 6 < (discriminant23CharacterFold w).re := by
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  rcases hr with hr | hr
  · have hRe : w.re ∈ Icc (0 : ℝ) 1 := ⟨hr.1, by linarith only [hr.2]⟩
    exact eight_sign_of_cells .rePositive false (n := 0) left_positive_check
      (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hRe hAbs
  · have hRe : w.re ∈ Icc (0 : ℝ) 1 := ⟨by linarith only [hr.1], hr.2⟩
    exact eight_sign_of_cells .rePositive false (n := 0) right_positive_check
      (w := w) (by norm_num; exact hr) (by norm_num; exact ht) hRe hAbs

theorem discriminant23_eight_above_positive {w : ℂ} (hr : w.re ∈ Icc (0 : ℝ) 1)
    (ht : w.im ∈ Icc (59 / 8 : ℝ) 8) : 2 / 10 ^ 6 < (discriminant23CharacterFold w).re := by
  have hAbs : |w.im| ≤ 8 := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
  by_cases hSide : w.re ≤ 1 / 2
  · exact eight_sign_of_cells .rePositive false (n := 4) above_left_checks
      (w := w) (by norm_num; exact ⟨hr.1, hSide⟩) (by norm_num; exact ht) hr hAbs
  · exact eight_sign_of_cells .rePositive false (n := 4) above_right_checks
      (w := w) (by norm_num; exact ⟨(lt_of_not_ge hSide).le, hr.2⟩) (by norm_num; exact ht) hr hAbs

#print axioms below_checks
#print axioms crossing_checks
#print axioms left_checks
#print axioms right_checks
#print axioms left_positive_check
#print axioms right_positive_check
#print axioms above_left_checks
#print axioms above_right_checks
#print axioms discriminant23_eight_below_negative
#print axioms discriminant23_eight_crossing_slope_negative
#print axioms discriminant23_eight_left_im_positive
#print axioms discriminant23_eight_right_im_negative
#print axioms discriminant23_eight_sides_re_positive
#print axioms discriminant23_eight_above_positive

end
end FieldTarget
