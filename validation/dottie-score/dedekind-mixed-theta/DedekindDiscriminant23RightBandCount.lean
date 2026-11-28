import DedekindDiscriminant23TwentyCount
import Gauss23Height20RightCover
import Gauss23Height21Values
import Gauss23Height21RightCover
import Gauss23Height22Values
import Gauss23Height22RightCover
import Gauss23Height23Values
import Gauss23Height23RightCover
import Gauss23Height24Values
import Gauss23Height24RightCover
import Gauss23Height25Values
import Gauss23Height25RightCover
import Gauss23Height26Values
import Gauss23Height26RightCover
import Gauss23Height27Values
import Gauss23Height27RightCover
import Gauss23Height28Values
import Gauss23Height28RightCover

/-! The next 126 cells add seven reflected pairs to the exact height-20 count. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Finset DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

private def certifiedIncrement (k : ℕ) : Prop :=
  discriminant23CharacterCountingFunction.HasStripZeroIncrement
    (gauss23RightHeight k) (gauss23RightHeight (k + 1)) (gauss23RightCover k).increment

private theorem right_increments (k : ℕ) (hk : k < 126) : certifiedIncrement k := by
  have hSegment (m start len : ℕ)
      (hValue : ∀ j ≤ 36, ComplexBox.Contains (gauss23RightValue m j)
          (gauss23CenteredCoeff false (m : ℝ) j))
      (hC : ∀ j : Fin len, gauss23RightCheck m (start + j.val) = true)
      (hlo : start ≤ k) (hhi : k < start + len) : certifiedIncrement k := by
    let j : Fin len := ⟨k - start, by omega⟩
    have hEq : start + j.val = k := by dsimp only [j]; omega
    exact hEq ▸ (gauss23_right_segment_of_checks m start len hValue hC j :
      certifiedIncrement (start + j.val))
  by_cases h20 : k < 8
  · exact hSegment 20 0 8 gauss23_right_values_at_20_contain gauss23_right_checks_at_20 (by omega) h20
  by_cases h21 : k < 24
  · exact hSegment 21 8 16 gauss23_right_values_at_21_contain gauss23_right_checks_at_21 (by omega) h21
  by_cases h22 : k < 40
  · exact hSegment 22 24 16 gauss23_right_values_at_22_contain gauss23_right_checks_at_22 (by omega) h22
  by_cases h23 : k < 56
  · exact hSegment 23 40 16 gauss23_right_values_at_23_contain gauss23_right_checks_at_23 (by omega) h23
  by_cases h24 : k < 72
  · exact hSegment 24 56 16 gauss23_right_values_at_24_contain gauss23_right_checks_at_24 (by omega) h24
  by_cases h25 : k < 88
  · exact hSegment 25 72 16 gauss23_right_values_at_25_contain gauss23_right_checks_at_25 (by omega) h25
  by_cases h26 : k < 104
  · exact hSegment 26 88 16 gauss23_right_values_at_26_contain gauss23_right_checks_at_26 (by omega) h26
  by_cases h27 : k < 119
  · exact hSegment 27 104 15 gauss23_right_values_at_27_contain gauss23_right_checks_at_27 (by omega) h27
  exact hSegment 28 119 7 gauss23_right_values_at_28_contain gauss23_right_checks_at_28 (by omega) hk

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem right_crossings_count :
    (∑ k ∈ Finset.range 126, (gauss23RightCover k).increment) = 7 := by
  decide +kernel

theorem discriminant23_strip_increment_to_447_div_16 :
    discriminant23CharacterCountingFunction.HasStripZeroIncrement 20 (447 / 16) 7 := by
  have h := discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_mesh gauss23RightHeight
    (fun k ↦ (gauss23RightCover k).increment) 126 right_increments
  simpa only [right_crossings_count,
    show gauss23RightHeight 0 = 20 by norm_num [gauss23RightHeight, gauss23RightCut, gauss23RightOrdinal],
    show gauss23RightHeight 126 = 447 / 16 by norm_num [gauss23RightHeight, gauss23RightCut, gauss23RightOrdinal]]
    using h

theorem discriminant23_character_counts_at_447_div_16 :
    discriminant23CharacterCountingFunction.stripZeroCount (447 / 16) (fun _ ↦ True) = 36 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (447 / 16) (fun w ↦ w.re = 1 / 2) = 36 := by
  have h := discriminant23_strip_increment_to_447_div_16
  constructor
  · rw [h _ (fun _ _ ↦ trivial), discriminant23_character_counts_at_twenty.1]
  · rw [h _ (fun _ e ↦ e), discriminant23_character_counts_at_twenty.2]

theorem discriminant23_character_line_through_447_div_16 {w : ℂ}
    (hx₀ : 0 < w.re) (hx₁ : w.re < 1) (hy : |w.im| ≤ 447 / 16)
    (hz : discriminant23CharacterFold w = 0) : w.re = 1 / 2 := by
  have hCount := discriminant23_character_counts_at_447_div_16
  exact (discriminant23CharacterCountingFunction.stripCounts_equal_iff (447 / 16)).mp
    (hCount.1.trans hCount.2.symm) w hx₀ hx₁ hy hz

theorem discriminant23_field_counts_at_447_div_16_add_seventy_two :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount (447 / 16) (fun _ ↦ True) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount (447 / 16)
        (fun _ ↦ True) + 72 ∧
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount (447 / 16)
      (fun w ↦ w.re = 1 / 2) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount (447 / 16)
        (fun w ↦ w.re = 1 / 2) + 72 := by
  have h := discriminant23_character_counts_at_447_div_16
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character, h.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character, h.2]

theorem discriminant23_dedekindRH_iff_character_above_447_div_16
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔ ∀ w : ℂ,
      1 / 2 < w.re → w.re ≤ 7 / 8 → 447 / 16 < w.im → discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_above_twenty hD]
  constructor
  · intro h w hx₀ hx₁ hy
    exact h w hx₀ hx₁ (by linarith only [hy])
  · intro h w hx₀ hx₁ hy hz
    by_cases hHigh : 447 / 16 < w.im
    · exact h w hx₀ hx₁ hHigh hz
    · have hLine := discriminant23_character_line_through_447_div_16
        (by linarith only [hx₀]) (by linarith only [hx₁])
        (by rw [abs_of_nonneg (by linarith only [hy])]; exact le_of_not_gt hHigh) hz
      exact hx₀.ne' hLine

#check @discriminant23_character_counts_at_447_div_16
#check @discriminant23_field_counts_at_447_div_16_add_seventy_two
#check @discriminant23_dedekindRH_iff_character_above_447_div_16
#print axioms discriminant23_strip_increment_to_447_div_16
#print axioms discriminant23_character_counts_at_447_div_16
#print axioms discriminant23_character_line_through_447_div_16
#print axioms discriminant23_field_counts_at_447_div_16_add_seventy_two
#print axioms discriminant23_dedekindRH_iff_character_above_447_div_16

end

end FieldTarget
