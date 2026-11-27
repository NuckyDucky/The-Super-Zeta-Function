import DedekindDiscriminant23HigherPanel
import DedekindDiscriminant23SixBandSigns
import DedekindHighRightAfterCount

/-! Extend the character count from height 11/2 to height 6 using the same
sample and coefficient tables. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set
open DottieOriented.NativeSpectrum.MellinFixed
open scoped BigOperators

noncomputable section

private theorem argument_radius_to_six {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 6) : ‖discriminant23ReadingArgument w‖ ≤ 101 / 100 := by
  let z := discriminant23ReadingArgument w
  have hRe : |z.re| ≤ 1 / 12 := by
    rw [show z.re = (w.re - 1 / 2) / 6 from discriminant23_readingArgument_re w]
    exact abs_le.mpr ⟨by linarith only [hre.1], by linarith only [hre.2]⟩
  have hIm : |z.im| ≤ 1 := by
    rw [show z.im = w.im / 6 from discriminant23_readingArgument_im w, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 6), div_le_one (by norm_num)]
    exact him
  have hReSq := pow_le_pow_left₀ (abs_nonneg _) hRe 2
  have hImSq := pow_le_pow_left₀ (abs_nonneg _) hIm 2
  rw [sq_abs] at hReSq hImSq
  have hsq : ‖z‖ ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [hReSq, hImSq]
  change ‖z‖ ≤ 101 / 100
  nlinarith only [hsq, norm_nonneg z]

private theorem reading_tail_to_six {w : ℂ} (hz : ‖discriminant23ReadingArgument w‖ ≤ 101 / 100) :
    ‖discriminant23ReadingTaylor false w - discriminant23ReadingPartialTaylor false w‖ ≤
      55 / 1000000 := by
  have h := ComplexBox.polynomial_tail_le_of_weighted_mass
    (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox false k))
    (fun k ↦ (discriminant23ReadingCoefficient false k : ℂ))
    (p := 101) (q := 100) (m := discriminant23ReadingTerms) (n := 72)
    (budget := 55 * 10 ^ 18) (by decide) (by decide)
    (by simpa only [Nat.cast_ofNat] using hz)
    (fun k _ ↦ ComplexBox.real_contains (discriminant23_storedReadingCoefficientBox_contains false k))
    discriminant23_value_weighted_tail_at_101_over_100
  have hBudget : ((55 * 10 ^ 18 : ℤ) : ℝ) / (scale : ℝ) = 55 / 1000000 := by norm_num [scale]
  rw [hBudget] at h
  exact h

private theorem folded_reading_error_to_six {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : |w.im| ≤ 6) :
    ‖discriminant23CharacterFold w - discriminant23ReadingPartialTaylor false w‖ ≤
      548 / 1000000 := by
  have hz := argument_radius_to_six hre him
  have hQuad := discriminant23_value_quadrature_bound_to_six hre.1 hre.2 him
  have hTaylor : ‖discriminant23CharacterComplexModel w - discriminant23ReadingTaylor false w‖ ≤
      483 / 1000000 := by
    refine (discriminant23_value_taylor_error_of_quadrature (R := 19) hre.1 hre.2 (by norm_num)
      (by linarith only [hz]) hQuad).trans ?_
    norm_num [Nat.factorial]
  have hModel := discriminant23_characterComplexModel_error (w := w)
    (by linarith only [hre.1]) (by linarith only [hre.2])
  have hTail := reading_tail_to_six hz
  refine (norm_sub_le_norm_sub_add_norm_sub _ (discriminant23CharacterComplexModel w) _).trans ?_
  have hLast := (norm_sub_le_norm_sub_add_norm_sub _ (discriminant23ReadingTaylor false w) _).trans
    (add_le_add hTaylor hTail)
  exact (add_le_add hModel hLast).trans (by norm_num)

private theorem upper_of_six_cell {b : Box} {x : ℝ} (hb : Contains b x)
    (hs : b.hi < -discriminant23SixBandMargin) : x < -(600 / 1000000) := by
  apply lt_of_box_upper hb
  have h : (scale : ℝ) * (-(600 / 1000000)) = (-(discriminant23SixBandMargin : ℤ) : ℝ) := by
    norm_num [scale, discriminant23SixBandMargin]
  rw [h]
  exact_mod_cast hs

private theorem partial_real_negative_in_six_band {w : ℂ} (hre : w.re ∈ Icc (0 : ℝ) 1)
    (him : w.im ∈ Icc (11 / 2 : ℝ) 6) :
    (discriminant23ReadingPartialTaylor false w).re < -(600 / 1000000) := by
  obtain ⟨j, hLow, hHigh⟩ :=
    real_mem_equal_closed_cells (11 / 2) (1 / 32) w.im 15 him.1 (by norm_num; exact him.2)
  have hIm₀ : (-1 : ℝ) / 384 ≤ (discriminant23ReadingArgument w).im -
      ((353 + 2 * (j.val : ℤ) : ℤ) : ℝ) / 384 := by
    rw [discriminant23_readingArgument_im]
    push_cast
    linarith only [hLow]
  have hIm₁ : (discriminant23ReadingArgument w).im -
      ((353 + 2 * (j.val : ℤ) : ℤ) : ℝ) / 384 ≤ 1 / 384 := by
    rw [discriminant23_readingArgument_im]
    push_cast
    linarith only [hHigh]
  have hCoeff := discriminant23_storedReadingCoefficientBox_contains false
  by_cases hs : w.re ≤ 1 / 2
  · have h := discriminant23_readingCellBox_contains
      (discriminant23StoredReadingCoefficientBox false) false hCoeff
      (w := w) (m := 353 + 2 * (j.val : ℤ)) (radius := 1) (d := 384) (left := -1) (right := 0)
      (by norm_num) (by rw [discriminant23_readingArgument_re]; linarith only [hre.1])
      (by rw [discriminant23_readingArgument_re]; norm_num; linarith only [hs])
      (by simpa using hIm₀) (by simpa using hIm₁)
    exact upper_of_six_cell h.1 (discriminant23_six_band_cell_signs false j)
  · have hs' := lt_of_not_ge hs
    have h := discriminant23_readingCellBox_contains
      (discriminant23StoredReadingCoefficientBox false) false hCoeff
      (w := w) (m := 353 + 2 * (j.val : ℤ)) (radius := 1) (d := 384) (left := 0) (right := 1)
      (by norm_num) (by rw [discriminant23_readingArgument_re]; norm_num; linarith only [hs'])
      (by rw [discriminant23_readingArgument_re]; linarith only [hre.2])
      (by simpa using hIm₀) (by simpa using hIm₁)
    exact upper_of_six_cell h.1 (discriminant23_six_band_cell_signs true j)

theorem discriminant23_character_re_negative_in_six_band {w : ℂ}
    (hre : w.re ∈ Icc (0 : ℝ) 1) (him : w.im ∈ Icc (11 / 2 : ℝ) 6) :
    (discriminant23CharacterFold w).re < -(52 / 1000000) := by
  have hAbs : |w.im| ≤ 6 := by
    rw [abs_of_nonneg (by linarith only [him.1])]
    exact him.2
  have hError := (abs_le.mp ((Complex.abs_re_le_norm _).trans
    (folded_reading_error_to_six hre hAbs))).2
  rw [Complex.sub_re] at hError
  linarith only [hError, partial_real_negative_in_six_band hre him]

theorem discriminant23_character_nonzero_in_six_band {w : ℂ}
    (hre : w.re ∈ Icc (0 : ℝ) 1) (hlo : 11 / 2 ≤ |w.im|) (hhi : |w.im| ≤ 6) :
    discriminant23CharacterFold w ≠ 0 := by
  have hSign : (discriminant23CharacterFold w).re < -(52 / 1000000) := by
    by_cases hpos : 0 ≤ w.im
    · rw [abs_of_nonneg hpos] at hlo hhi
      exact discriminant23_character_re_negative_in_six_band hre ⟨hlo, hhi⟩
    · rw [abs_of_neg (lt_of_not_ge hpos)] at hlo hhi
      have hre' : (1 - w).re ∈ Icc (0 : ℝ) 1 := by
        rw [Complex.sub_re, Complex.one_re]
        exact ⟨by linarith only [hre.2], by linarith only [hre.1]⟩
      have him' : (1 - w).im ∈ Icc (11 / 2 : ℝ) 6 := by
        simpa only [mem_Icc, Complex.sub_im, Complex.one_im, zero_sub] using And.intro hlo hhi
      have h := discriminant23_character_re_negative_in_six_band hre' him'
      rw [discriminant23_characterFold_one_sub] at h
      exact h
  intro hzero
  rw [hzero, Complex.zero_re] at hSign
  norm_num at hSign

theorem discriminant23_character_counts_at_six :
    discriminant23CharacterCountingFunction.stripZeroCount 6 (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount 6 (fun w ↦ w.re = 1 / 2) = 2 := by
  have hSet : discriminant23CharacterCountingFunction.stripZeros 6 =
      discriminant23CharacterCountingFunction.stripZeros (11 / 2) := by
    ext w
    rw [NonzeroEntireFunction.mem_stripZeros, NonzeroEntireFunction.mem_stripZeros]
    change (0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ 6 ∧ discriminant23CharacterFold w = 0) ↔
      (0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ 11 / 2 ∧ discriminant23CharacterFold w = 0)
    constructor
    · rintro ⟨hre, hhi, ht, hz⟩
      refine ⟨hre, hhi, ?_, hz⟩
      by_contra hT
      exact discriminant23_character_nonzero_in_six_band ⟨hre.le, hhi.le⟩
        (le_of_lt (lt_of_not_ge hT)) ht hz
    · rintro ⟨hre, hhi, ht, hz⟩
      exact ⟨hre, hhi, by linarith only [ht], hz⟩
  have hCount (P : ℂ → Prop) : discriminant23CharacterCountingFunction.stripZeroCount 6 P =
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) P := by
    simp only [NonzeroEntireFunction.stripZeroCount, hSet]
  exact ⟨(hCount _).trans discriminant23_character_counts_at_eleven_halves.1,
    (hCount _).trans discriminant23_character_counts_at_eleven_halves.2⟩

theorem discriminant23_field_counts_at_six_add_four :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 6 (fun _ ↦ True) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 6
          (fun _ ↦ True) + 4 ∧
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 6 (fun w ↦ w.re = 1 / 2) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 6
          (fun w ↦ w.re = 1 / 2) + 4 := by
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character, discriminant23_character_counts_at_six.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character, discriminant23_character_counts_at_six.2]

theorem discriminant23_dedekindRH_iff_character_above_six
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → 6 < |w.im| →
        discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_high_right hD]
  constructor
  · intro h w hre hhi ht
    exact h w hre hhi (by linarith only [ht])
  · intro h w hre hhi ht
    by_cases hT : |w.im| ≤ 6
    · exact discriminant23_character_nonzero_in_six_band
        ⟨by linarith only [hre], by linarith only [hhi]⟩ ht.le hT
    · exact h w hre hhi (lt_of_not_ge hT)

#check @discriminant23_character_counts_at_six
#check @discriminant23_field_counts_at_six_add_four
#check @discriminant23_dedekindRH_iff_character_above_six
#print axioms discriminant23_character_re_negative_in_six_band
#print axioms discriminant23_character_nonzero_in_six_band
#print axioms discriminant23_character_counts_at_six
#print axioms discriminant23_field_counts_at_six_add_four
#print axioms discriminant23_dedekindRH_iff_character_above_six

end

end FieldTarget
