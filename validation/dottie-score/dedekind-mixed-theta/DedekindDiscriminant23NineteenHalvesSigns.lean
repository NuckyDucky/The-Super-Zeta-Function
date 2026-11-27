import DedekindDiscriminant23NineteenHalvesError
import DedekindDiscriminant23NineteenHalvesWings
import DedekindDiscriminant23NineteenHalvesUpperCells

namespace FieldTarget

open Complex Set
open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

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

private def Sign.check (s : Sign) (m : ℤ) (b : ComplexBox) : Prop :=
  match s with
  | .rePositive => m < b.re.lo
  | .reNegative => b.re.hi < -m
  | .imPositive => m < b.im.lo
  | .imNegative => b.im.hi < -m

private theorem Sign.read_gt_of_check {s : Sign} {m : ℤ} {b : ComplexBox} {z : ℂ}
    (h : ComplexBox.Contains b z) (hcheck : s.check m b) : (m : ℝ) / scale < s.read z := by
  have lower {B : Box} {x : ℝ} (hx : Contains B x) (hb : m < B.lo) : (m : ℝ) / scale < x := by
    apply lt_of_box_lower hx
    rw [show (scale : ℝ) * ((m : ℝ) / scale) = (m : ℝ) by field_simp [ne_of_gt scale_pos]]
    exact_mod_cast hb
  have upper {B : Box} {x : ℝ} (hx : Contains B x) (hb : B.hi < -m) : (m : ℝ) / scale < -x := by
    have ho : x < -((m : ℝ) / scale) := by
      apply lt_of_box_upper hx
      rw [show (scale : ℝ) * -((m : ℝ) / scale) = ((-m : ℤ) : ℝ) by
        rw [Int.cast_neg]
        field_simp [ne_of_gt scale_pos]]
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

private theorem cell_contains (odd : Bool) {k : ℕ} {l r : ℤ} {w : ℂ}
    (hr : w.re ∈ Icc (1 / 2 + (l : ℝ) / 4) (1 / 2 + (r : ℝ) / 4))
    (ht : w.im ∈ Icc ((k : ℝ) / 8) (((k : ℝ) + 1) / 8)) :
    ComplexBox.Contains (discriminant23NineteenHalvesCell odd k l r)
      (discriminant23ReadingTaylorUpTo odd 68 w) := by
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

private def margin (odd : Bool) : ℤ := if odd then 2 * 10 ^ 18 else 6 * 10 ^ 17

private theorem signed_reading_of_cells (sign : Sign) (odd : Bool) {start n : ℕ} {l r : ℤ} {w : ℂ}
    (hCheck : ∀ j : Fin (n + 1), sign.check (margin odd)
      (discriminant23NineteenHalvesCell odd (start + j.val) l r))
    (hr : w.re ∈ Icc (1 / 2 + (l : ℝ) / 4) (1 / 2 + (r : ℝ) / 4))
    (ht : w.im ∈ Icc ((start : ℝ) / 8) (((start : ℝ) + n + 1) / 8))
    (hre : w.re ∈ Icc (0 : ℝ) 1) (him : |w.im| ≤ 19 / 2) :
    0 < sign.read (if odd then deriv discriminant23CharacterFold w else
      discriminant23CharacterFold w) := by
  obtain ⟨j, hj₀, hj₁⟩ := real_mem_equal_closed_cells ((start : ℝ) / 8) (1 / 8) w.im n ht.1
    (by push_cast; linarith only [ht.2])
  have hCell := cell_contains odd hr (k := start + j.val) (w := w) (by
    push_cast
    exact ⟨by linarith only [hj₀], by linarith only [hj₁]⟩)
  have hRead := Sign.read_gt_of_check hCell (hCheck j)
  have hErr : ‖(if odd then deriv discriminant23CharacterFold w else
      discriminant23CharacterFold w) - discriminant23ReadingTaylorUpTo odd 68 w‖ ≤
        (margin odd : ℝ) / scale := by
    have h := discriminant23_reading_error_to_nineteen_halves hre him
    cases odd
    · exact h.1.trans (by norm_num [margin, scale])
    · exact h.2.trans (by norm_num [margin, scale])
  have hδ := (abs_le.mp ((sign.abs_read_le_norm _).trans hErr)).1
  rw [sign.read_sub] at hδ
  linarith only [hRead, hδ]

private theorem abs_height_le {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 19 / 2)
    (ht : t ∈ Icc a b) : |t| ≤ 19 / 2 := by
  rw [abs_of_nonneg (ha.trans ht.1)]
  exact ht.2.trans hb

theorem discriminant23_nineteenHalves_below_positive {w : ℂ}
    (hr : w.re ∈ Icc (0 : ℝ) 1) (ht : w.im ∈ Icc (8 : ℝ) (67 / 8)) :
    0 < (discriminant23CharacterFold w).re := by
  exact signed_reading_of_cells .rePositive false (start := 64) (n := 2) (l := -2) (r := 2)
    discriminant23_nineteenHalves_below_checks
    (by convert hr using 1; norm_num) (by convert ht using 1; norm_num) hr
    (abs_height_le (by norm_num) (by norm_num) ht)

theorem discriminant23_nineteenHalves_slope_positive {w : ℂ}
    (hr : w.re ∈ Icc (1 / 4 : ℝ) (3 / 4)) (ht : w.im ∈ Icc (67 / 8 : ℝ) 9) :
    0 < (deriv discriminant23CharacterFold w).im := by
  exact signed_reading_of_cells .imPositive true (start := 67) (n := 4) (l := -1) (r := 1)
    discriminant23_nineteenHalves_slope_checks
    (by convert hr using 1; norm_num) (by convert ht using 1; norm_num)
    ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    (abs_height_le (by norm_num) (by norm_num) ht)

theorem discriminant23_nineteenHalves_left_negative {w : ℂ}
    (hr : w.re ∈ Icc (0 : ℝ) (1 / 4)) (ht : w.im ∈ Icc (67 / 8 : ℝ) 9) :
    (discriminant23CharacterFold w).im < 0 := by
  have h := signed_reading_of_cells .imNegative false (start := 67) (n := 4) (l := -2) (r := -1)
    discriminant23_nineteenHalves_left_checks
    (by convert hr using 1; norm_num) (by convert ht using 1; norm_num)
    ⟨hr.1, by linarith only [hr.2]⟩ (abs_height_le (by norm_num) (by norm_num) ht)
  change 0 < -(discriminant23CharacterFold w).im at h
  linarith only [h]

theorem discriminant23_nineteenHalves_right_positive {w : ℂ}
    (hr : w.re ∈ Icc (3 / 4 : ℝ) 1) (ht : w.im ∈ Icc (67 / 8 : ℝ) 9) :
    0 < (discriminant23CharacterFold w).im := by
  exact signed_reading_of_cells .imPositive false (start := 67) (n := 4) (l := 1) (r := 2)
    discriminant23_nineteenHalves_right_checks
    (by convert hr using 1; norm_num) (by convert ht using 1; norm_num)
    ⟨by linarith only [hr.1], hr.2⟩ (abs_height_le (by norm_num) (by norm_num) ht)

theorem discriminant23_nineteenHalves_above_negative {w : ℂ}
    (hr : w.re ∈ Icc (0 : ℝ) 1) (ht : w.im ∈ Icc (9 : ℝ) (19 / 2)) :
    (discriminant23CharacterFold w).re < 0 := by
  have hIm := abs_height_le (by norm_num) le_rfl ht
  have ht' : w.im ∈ Icc ((72 : ℝ) / 8) (((72 : ℝ) + (3 : ℕ) + 1) / 8) := by
    convert ht using 1
    norm_num
  rcases le_or_gt w.re (1 / 2) with hL | hR
  · have h := signed_reading_of_cells .reNegative false (start := 72) (n := 3) (l := -2) (r := 0)
      discriminant23_nineteenHalves_above_left_checks
      (by norm_num; exact ⟨hr.1, hL⟩) ht' hr hIm
    change 0 < -(discriminant23CharacterFold w).re at h
    linarith only [h]
  · have h := signed_reading_of_cells .reNegative false (start := 72) (n := 3) (l := 0) (r := 2)
      discriminant23_nineteenHalves_above_right_checks
      (by norm_num; exact ⟨hR.le, hr.2⟩) ht' hr hIm
    change 0 < -(discriminant23CharacterFold w).re at h
    linarith only [h]

end

#print axioms discriminant23_nineteenHalves_below_positive
#print axioms discriminant23_nineteenHalves_slope_positive
#print axioms discriminant23_nineteenHalves_left_negative
#print axioms discriminant23_nineteenHalves_right_positive
#print axioms discriminant23_nineteenHalves_above_negative

end FieldTarget
