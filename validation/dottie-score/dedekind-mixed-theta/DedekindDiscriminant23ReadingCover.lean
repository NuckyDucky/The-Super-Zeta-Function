import DedekindDiscriminant23ReadingTail

/-! The fixed cover reduces the zero count to three finite integer tests. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed
open Set

noncomputable section

theorem real_mem_equal_closed_cells (a d t : ℝ) (n : ℕ) (h₀ : a ≤ t)
    (h₁ : t ≤ a + ((n + 1 : ℕ) : ℝ) * d) :
    ∃ j : Fin (n + 1), a + (j.val : ℝ) * d ≤ t ∧ t ≤ a + ((j.val : ℝ) + 1) * d := by
  induction n with
  | zero =>
    exact ⟨0, by simpa using h₀, by simpa using h₁⟩
  | succ n ih =>
    by_cases h : t ≤ a + ((n + 1 : ℕ) : ℝ) * d
    · obtain ⟨j, hj₀, hj₁⟩ := ih h
      exact ⟨j.castSucc, hj₀, hj₁⟩
    · refine ⟨Fin.last (n + 1), le_of_lt (lt_of_not_ge h), ?_⟩
      simpa only [Fin.val_last, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using h₁

theorem discriminant23_readingArgument_re (w : ℂ) :
    (discriminant23ReadingArgument w).re = (w.re - 1 / 2) / 6 := by
  unfold discriminant23ReadingArgument
  norm_num [Complex.div_re, Complex.sub_re, Complex.normSq_apply]

theorem discriminant23_readingArgument_im (w : ℂ) :
    (discriminant23ReadingArgument w).im = w.im / 6 := by
  unfold discriminant23ReadingArgument
  norm_num [Complex.div_im, Complex.sub_im, Complex.normSq_apply]

private theorem argument_re_bounds {w : ℂ} (hr : w.re ∈ Icc (0 : ℝ) 1) :
    (-1 : ℝ) / 12 ≤ (discriminant23ReadingArgument w).re ∧
      (discriminant23ReadingArgument w).re ≤ (1 : ℝ) / 12 := by
  rw [discriminant23_readingArgument_re]
  exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩

private theorem projection_error (odd : Bool) {w : ℂ} (hr : w.re ∈ Icc (0 : ℝ) 1)
    (ht : w.im ∈ Icc (0 : ℝ) (11 / 2)) :
    |(discriminant23ReadingTaylor odd w).re - (discriminant23ReadingPartialTaylor odd w).re| ≤
        40 / 1000000 ∧
      |(discriminant23ReadingTaylor odd w).im - (discriminant23ReadingPartialTaylor odd w).im| ≤
        40 / 1000000 := by
  have hr' : |(discriminant23ReadingArgument w).re| ≤ 1 / 12 :=
    abs_le.mpr ⟨by linarith only [(argument_re_bounds hr).1], (argument_re_bounds hr).2⟩
  have hi : |(discriminant23ReadingArgument w).im| ≤ 11 / 12 := by
    rw [discriminant23_readingArgument_im, abs_of_nonneg (div_nonneg ht.1 (by norm_num))]
    linarith only [ht.2]
  have hz : ‖discriminant23ReadingArgument w‖ ≤ 1 :=
    (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith only [hr', hi])
  have h := discriminant23_reading_partial_error_le odd hz
  exact ⟨by simpa only [Complex.sub_re] using (Complex.abs_re_le_norm _).trans h,
    by simpa only [Complex.sub_im] using (Complex.abs_im_le_norm _).trans h⟩

private theorem margin_as_real :
    (discriminant23ReadingMargin : ℝ) = (scale : ℝ) * (83 / 1000000) := by
  norm_num [discriminant23ReadingMargin, scale]

private theorem margin_lower {b : Box} {short full : ℝ} (hx : Contains b short)
    (h : discriminant23ReadingMargin < b.lo) (he : |full - short| ≤ 40 / 1000000) :
    43 / 1000000 < full := by
  have hm : 83 / 1000000 < short := by
    apply lt_of_box_lower hx
    rw [← margin_as_real]
    exact_mod_cast h
  linarith only [hm, (abs_le.mp he).1]

private theorem margin_upper {b : Box} {short full : ℝ} (hx : Contains b short)
    (h : b.hi < -discriminant23ReadingMargin) (he : |full - short| ≤ 40 / 1000000) :
    full < -(43 / 1000000) := by
  have hm : short < -(83 / 1000000) := by
    apply lt_of_box_upper hx
    rw [mul_neg, ← margin_as_real]
    exact_mod_cast h
  linarith only [hm, (abs_le.mp he).2]

/-- Provided the integer cells pass, both complete character counts are two.
The hypotheses are finite integer inequalities together with the reusable
containment statements for the coefficient rows. -/
theorem discriminant23_character_counts_of_integer_cells (value slope : ℕ → Box)
    (hValue : ∀ k, Contains (value k) (discriminant23ReadingCoefficient false k))
    (hSlope : ∀ k, Contains (slope k) (discriminant23ReadingCoefficient true k))
    (hBelow : ∀ j : Fin 16, discriminant23ReadingMargin < (discriminant23BelowBox value j).re.lo)
    (hMiddle : ∀ j : Fin 14, discriminant23ReadingMargin < (discriminant23SlopeBox slope j).im.lo)
    (hAbove : ∀ (rightSide : Bool) (j : Fin 8),
      (discriminant23AboveBox value rightSide j).re.hi < -discriminant23ReadingMargin) :
    discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) = 2 := by
  refine discriminant23_character_counts_of_taylor_signs ?_ ?_ ?_
  · intro w hr ht
    obtain ⟨j, hLow, hHigh⟩ := real_mem_equal_closed_cells (7 / 6) (5 / 24) w.im 15 ht.1
      (by norm_num; exact ht.2)
    have h := discriminant23_readingCellBox_contains value false hValue
      (w := w)
      (m := 61 + 10 * (j.val : ℤ)) (radius := 5) (d := 288) (left := -1) (right := 1)
      (by norm_num) (by simpa using (argument_re_bounds hr).1)
      (by simpa using (argument_re_bounds hr).2)
      (by rw [discriminant23_readingArgument_im]; push_cast; linarith only [hLow])
      (by rw [discriminant23_readingArgument_im]; push_cast; linarith only [hHigh])
    have hError := (projection_error false hr
      ⟨by linarith only [ht.1], by linarith only [ht.2]⟩).1
    exact margin_lower h.1 (hBelow j) hError
  · intro w hr ht
    obtain ⟨j, hLow, hHigh⟩ := real_mem_equal_closed_cells (83 / 16) (5 / 128) w.im 7 ht.1
      (by norm_num; exact ht.2)
    have hImag₀ : (-5 : ℝ) / 1536 ≤ (discriminant23ReadingArgument w).im -
        ((1333 + 10 * (j.val : ℤ) : ℤ) : ℝ) / 1536 := by
      rw [discriminant23_readingArgument_im]
      push_cast
      linarith only [hLow]
    have hImag₁ : (discriminant23ReadingArgument w).im -
        ((1333 + 10 * (j.val : ℤ) : ℤ) : ℝ) / 1536 ≤ 5 / 1536 := by
      rw [discriminant23_readingArgument_im]
      push_cast
      linarith only [hHigh]
    have hError := (projection_error false hr ⟨by linarith only [ht.1], ht.2⟩).1
    by_cases hs : w.re ≤ 1 / 2
    · have h := discriminant23_readingCellBox_contains value false hValue
        (w := w)
        (m := 1333 + 10 * (j.val : ℤ)) (radius := 5) (d := 1536) (left := -1) (right := 0)
        (by norm_num) (by simpa using (argument_re_bounds hr).1)
        (by rw [discriminant23_readingArgument_re]; norm_num; linarith only [hs])
        (by simpa using hImag₀)
        (by simpa using hImag₁)
      exact margin_upper h.1 (hAbove false j) hError
    · have hs' : (1 / 2 : ℝ) < w.re := lt_of_not_ge hs
      have h := discriminant23_readingCellBox_contains value false hValue
        (w := w)
        (m := 1333 + 10 * (j.val : ℤ)) (radius := 5) (d := 1536) (left := 0) (right := 1)
        (by norm_num) (by rw [discriminant23_readingArgument_re]; norm_num; linarith only [hs'])
        (by simpa using (argument_re_bounds hr).2) (by simpa using hImag₀) (by simpa using hImag₁)
      exact margin_upper h.1 (hAbove true j) hError
  · intro w hr ht
    obtain ⟨j, hLow, hHigh⟩ := real_mem_equal_closed_cells (9 / 2) (11 / 224) w.im 13 ht.1
      (by norm_num; exact ht.2)
    have h := discriminant23_readingCellBox_contains slope true hSlope
      (w := w)
      (m := 2027 + 22 * (j.val : ℤ)) (radius := 11) (d := 2688) (left := -1) (right := 1)
      (by norm_num) (by simpa using (argument_re_bounds hr).1)
      (by simpa using (argument_re_bounds hr).2)
      (by rw [discriminant23_readingArgument_im]; push_cast; linarith only [hLow])
      (by rw [discriminant23_readingArgument_im]; push_cast; linarith only [hHigh])
    have hError := (projection_error true hr
      ⟨by linarith only [ht.1], by linarith only [ht.2]⟩).2
    exact margin_lower h.2 (hMiddle j) hError

#check @discriminant23_character_counts_of_integer_cells
#print axioms discriminant23_character_counts_of_integer_cells

end

end FieldTarget

