import ComplexStripSingleZero
import ComplexStripCrossingCount
import DedekindDiscriminant23NineteenHalvesSigns
import DedekindDiscriminant23EightBand

/-! The third crossing and complete character count through height 19/2. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set

noncomputable section

theorem discriminant23_crossing_between_eight_and_nineteen_halves :
    ∃ t ∈ Ioo (67 / 8 : ℝ) 9,
      analyticOrderNatAt discriminant23CharacterFold ⟨1 / 2, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (8 : ℝ) (19 / 2) →
        (discriminant23CharacterFold w = 0 ↔ w = ⟨1 / 2, t⟩) := by
  refine strip_zero_unique_of_signed_core discriminant23CharacterFold_differentiable
    (l := 1 / 4) (r := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by constructor <;> norm_num) (by norm_num)
    (fun _ hr ht ↦ discriminant23_nineteenHalves_below_positive hr ht)
    (fun _ hr ht ↦ discriminant23_nineteenHalves_above_negative hr ht)
    ?_ (fun _ hr ht ↦ discriminant23_nineteenHalves_slope_positive hr ht)
    (fun t _ ↦ discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl)
  intro w hr ht hZero
  constructor
  · by_contra! h
    have hSign := discriminant23_nineteenHalves_left_negative ⟨hr.1, h.le⟩ ht
    rw [hZero, Complex.zero_im] at hSign
    exact (lt_irrefl _ hSign)
  · by_contra! h
    have hSign := discriminant23_nineteenHalves_right_positive ⟨h.le, hr.2⟩ ht
    rw [hZero, Complex.zero_im] at hSign
    exact (lt_irrefl _ hSign)

theorem discriminant23_character_counts_at_nineteen_halves :
    discriminant23CharacterCountingFunction.stripZeroCount (19 / 2) (fun _ ↦ True) = 6 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (19 / 2)
        (fun w ↦ w.re = 1 / 2) = 6 := by
  obtain ⟨t, ht, hSimple, hUnique⟩ := discriminant23_crossing_between_eight_and_nineteen_halves
  have hCount (P : ℂ → Prop) (hP : ∀ w : ℂ, w.re = 1 / 2 → P w) :
      discriminant23CharacterCountingFunction.stripZeroCount (19 / 2) P =
        discriminant23CharacterCountingFunction.stripZeroCount 8 P + 2 :=
    discriminant23CharacterCountingFunction.stripZeroCount_add_reflected_crossing
      (by norm_num) (by linarith only [ht.1]) (by linarith only [ht.2])
      discriminant23_characterFold_one_sub
      (fun w hw hi ↦ hUnique w (Ioo_subset_Icc_self hw) ⟨hi.1.le, hi.2⟩) hSimple P hP
  constructor
  · rw [hCount _ (fun _ _ ↦ trivial), discriminant23_character_counts_at_eight.1]
  · rw [hCount _ (fun _ h ↦ h), discriminant23_character_counts_at_eight.2]

theorem discriminant23_field_counts_at_nineteen_halves_add_twelve :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount (19 / 2)
        (fun _ ↦ True) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount
          (19 / 2) (fun _ ↦ True) + 12 ∧
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount (19 / 2)
        (fun w ↦ w.re = 1 / 2) =
        (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount
          (19 / 2) (fun w ↦ w.re = 1 / 2) + 12 := by
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character,
        discriminant23_character_counts_at_nineteen_halves.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character,
        discriminant23_character_counts_at_nineteen_halves.2]

theorem discriminant23_dedekindRH_iff_character_above_nineteen_halves
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → 19 / 2 < |w.im| →
        discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_above_eight hD]
  constructor
  · intro h w hlo hhi ht
    exact h w hlo hhi (by linarith only [ht])
  · intro h w hlo hhi ht hz
    by_cases hs : |w.im| ≤ 19 / 2
    · have hLine := (discriminant23CharacterCountingFunction.stripCounts_equal_iff (19 / 2)).mp
        (discriminant23_character_counts_at_nineteen_halves.1.trans
          discriminant23_character_counts_at_nineteen_halves.2.symm)
        w (by linarith only [hlo]) (by linarith only [hhi]) hs hz
      exact (ne_of_gt hlo) hLine
    · exact h w hlo hhi (lt_of_not_ge hs) hz

#check @discriminant23_character_counts_at_nineteen_halves
#check @discriminant23_field_counts_at_nineteen_halves_add_twelve
#check @discriminant23_dedekindRH_iff_character_above_nineteen_halves
#print axioms discriminant23_crossing_between_eight_and_nineteen_halves
#print axioms discriminant23_character_counts_at_nineteen_halves
#print axioms discriminant23_field_counts_at_nineteen_halves_add_twelve
#print axioms discriminant23_dedekindRH_iff_character_above_nineteen_halves

end
end FieldTarget
