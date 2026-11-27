import ComplexStripSingleZero
import ComplexStripCrossingCount
import DedekindDiscriminant23EightSigns
import DedekindDiscriminant23SixBand

/-! A second simple crossing and the complete character count through height 8. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set

noncomputable section

theorem discriminant23_crossing_between_six_and_eight :
    ∃ t ∈ Ioo (13 / 2 : ℝ) (59 / 8),
      analyticOrderNatAt discriminant23CharacterFold ⟨1 / 2, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (6 : ℝ) 8 →
        (discriminant23CharacterFold w = 0 ↔ w = ⟨1 / 2, t⟩) := by
  obtain ⟨t, ht, hSimple, hUnique⟩ := unique_simple_zero_of_signed_crossing
    (f := discriminant23CharacterFold) (l := 1 / 4) (σ := 1 / 2) (r := 3 / 4)
    (a := 13 / 2) (b := 59 / 8) (direction := -1)
    (fun w _ _ ↦ discriminant23CharacterFold_differentiable.analyticAt w)
    (by constructor <;> norm_num) (by norm_num) (by
      have h := discriminant23_eight_below_negative (w := ⟨1 / 2, 13 / 2⟩)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
      linarith only [h]) (by
      have h := discriminant23_eight_above_positive (w := ⟨1 / 2, 59 / 8⟩)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
      linarith only [h])
    (fun w hr hi ↦ by linarith only [discriminant23_eight_crossing_slope_negative hr hi])
    (fun t _ ↦ discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl)
  refine ⟨t, ht, hSimple, fun w hr him ↦ ⟨?_, ?_⟩⟩
  · intro hz
    have hMid : w.im ∈ Icc (13 / 2 : ℝ) (59 / 8) := by
      constructor
      · by_contra! h
        have hSign := discriminant23_eight_below_negative hr ⟨him.1, h.le⟩
        rw [hz, Complex.zero_re] at hSign
        norm_num at hSign
      · by_contra! h
        have hSign := discriminant23_eight_above_positive hr ⟨h.le, him.2⟩
        rw [hz, Complex.zero_re] at hSign
        norm_num at hSign
    have hCentral : w.re ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
      by_contra h
      have hSide : w.re ∈ Icc (0 : ℝ) (1 / 4) ∨ w.re ∈ Icc (3 / 4 : ℝ) 1 := by
        simp only [mem_Icc, not_and_or, not_le] at h
        exact h.elim (fun h ↦ .inl ⟨hr.1, h.le⟩) (fun h ↦ .inr ⟨h.le, hr.2⟩)
      by_cases hCut : w.im ≤ 29 / 4
      · rcases hSide with hl | hh
        · have hs := discriminant23_eight_left_im_positive hl ⟨hMid.1, hCut⟩
          rw [hz, Complex.zero_im] at hs
          norm_num at hs
        · have hs := discriminant23_eight_right_im_negative hh ⟨hMid.1, hCut⟩
          rw [hz, Complex.zero_im] at hs
          norm_num at hs
      · have hs := discriminant23_eight_sides_re_positive hSide ⟨(lt_of_not_ge hCut).le, hMid.2⟩
        rw [hz, Complex.zero_re] at hs
        norm_num at hs
    exact (hUnique w hCentral hMid).mp hz
  · rintro rfl
    exact (hUnique ⟨1 / 2, t⟩ (by constructor <;> norm_num) (Ioo_subset_Icc_self ht)).mpr rfl

theorem discriminant23_character_counts_at_eight :
    discriminant23CharacterCountingFunction.stripZeroCount 8 (fun _ ↦ True) = 4 ∧
      discriminant23CharacterCountingFunction.stripZeroCount 8 (fun w ↦ w.re = 1 / 2) = 4 := by
  obtain ⟨t, ht, hSimple, hUnique⟩ := discriminant23_crossing_between_six_and_eight
  have hCount (P : ℂ → Prop) (hP : ∀ w : ℂ, w.re = 1 / 2 → P w) :
      discriminant23CharacterCountingFunction.stripZeroCount 8 P =
        discriminant23CharacterCountingFunction.stripZeroCount 6 P + 2 :=
    discriminant23CharacterCountingFunction.stripZeroCount_add_reflected_crossing
      (by norm_num) (by linarith only [ht.1]) (by linarith only [ht.2])
      discriminant23_characterFold_one_sub
      (fun w hw hi ↦ hUnique w (Ioo_subset_Icc_self hw) ⟨hi.1.le, hi.2⟩) hSimple P hP
  constructor
  · rw [hCount _ (fun _ _ ↦ trivial), discriminant23_character_counts_at_six.1]
  · rw [hCount _ (fun _ h ↦ h), discriminant23_character_counts_at_six.2]

theorem discriminant23_field_counts_at_eight_add_eight :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 8 (fun _ ↦ True) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 8
          (fun _ ↦ True) + 8 ∧
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 8 (fun w ↦ w.re = 1 / 2) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 8
          (fun w ↦ w.re = 1 / 2) + 8 := by
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character, discriminant23_character_counts_at_eight.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character, discriminant23_character_counts_at_eight.2]

theorem discriminant23_dedekindRH_iff_character_above_eight
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → 8 < |w.im| →
        discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_above_six hD]
  constructor
  · intro h w hlo hhi ht
    exact h w hlo hhi (by linarith only [ht])
  · intro h w hlo hhi ht hz
    by_cases hs : |w.im| ≤ 8
    · have hLine := (discriminant23CharacterCountingFunction.stripCounts_equal_iff 8).mp
        (discriminant23_character_counts_at_eight.1.trans discriminant23_character_counts_at_eight.2.symm)
        w (by linarith only [hlo]) (by linarith only [hhi]) hs hz
      exact (ne_of_gt hlo) hLine
    · exact h w hlo hhi (lt_of_not_ge hs) hz

#check @discriminant23_character_counts_at_eight
#check @discriminant23_field_counts_at_eight_add_eight
#check @discriminant23_dedekindRH_iff_character_above_eight
#print axioms discriminant23_crossing_between_six_and_eight
#print axioms discriminant23_character_counts_at_eight
#print axioms discriminant23_field_counts_at_eight_add_eight
#print axioms discriminant23_dedekindRH_iff_character_above_eight

end
end FieldTarget
