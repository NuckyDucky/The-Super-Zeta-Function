import ComplexStripCrossingMesh
import DedekindDiscriminant23SevenEighths
import DedekindDiscriminant23TwentyEndpointLogic

/-! The exact sign inputs for the interval replay through height 20 and their
consequences for the character and the Dedekind factorization. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set

noncomputable section

def Discriminant23TwentyBandConditions : Prop :=
  ∀ k < 168,
    let a := discriminant23TwentyHeight k
    let b := discriminant23TwentyHeight (k + 1)
    let d := discriminant23TwentyDirection k
    if d = 0 then
      ∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Ioc a b → discriminant23CharacterFold w ≠ 0
    else
      0 < (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, a⟩).re ∧
      (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, b⟩).re < 0 ∧
      (∀ w : ℂ, w.re ∈ Icc (3 / 8 : ℝ) (5 / 8) → w.im ∈ Icc a b →
        0 < (d : ℝ) * (deriv discriminant23CharacterFold w).im) ∧
      (∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Icc a b → discriminant23CharacterFold w = 0 →
        w.re ∈ Icc (3 / 8 : ℝ) (5 / 8))

/-- The rectangle obligations for one cell after supplying the endpoint signs. -/
def Discriminant23TwentyCellCondition (k : ℕ) : Prop :=
  let a := discriminant23TwentyHeight k
  let b := discriminant23TwentyHeight (k + 1)
  let d := discriminant23TwentyDirection k
  if d = 0 then
    ∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Ioc a b → discriminant23CharacterFold w ≠ 0
  else
    (∀ w : ℂ, w.re ∈ Icc (3 / 8 : ℝ) (5 / 8) → w.im ∈ Icc a b →
      0 < (d : ℝ) * (deriv discriminant23CharacterFold w).im) ∧
    (∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Icc a b → discriminant23CharacterFold w = 0 →
      w.re ∈ Icc (3 / 8 : ℝ) (5 / 8))

def Discriminant23TwentyCellConditions : Prop := ∀ k < 168, Discriminant23TwentyCellCondition k

theorem discriminant23_twentyBandConditions_iff :
    Discriminant23TwentyBandConditions ↔
      Discriminant23TwentyEndpointSigns ∧ Discriminant23TwentyCellConditions := by
  constructor
  · intro h
    constructor
    · intro k hk hd
      have hBand := h k hk
      dsimp only at hBand ⊢
      rw [ite_eq_right hd] at hBand
      exact ⟨hBand.1, hBand.2.1⟩
    · intro k hk
      have hBand := h k hk
      unfold Discriminant23TwentyCellCondition
      dsimp only at hBand ⊢
      by_cases hd : discriminant23TwentyDirection k = 0
      · simpa only [ite_eq_left hd] using hBand
      · simp only [ite_eq_right hd] at hBand ⊢
        exact hBand.2.2
  · rintro ⟨hSigns, hCells⟩ k hk
    have hCell := hCells k hk
    unfold Discriminant23TwentyCellCondition at hCell
    dsimp only at hCell ⊢
    by_cases hd : discriminant23TwentyDirection k = 0
    · simpa only [ite_eq_left hd] using hCell
    · simp only [ite_eq_right hd] at hCell ⊢
      obtain ⟨hA, hB⟩ := hSigns k hk hd
      exact ⟨hA, hB, hCell.1, hCell.2⟩

private def newCrossings (k : ℕ) : ℕ := if discriminant23TwentyDirection k = 0 then 0 else 1

set_option maxRecDepth 8192 in
private theorem sum_newCrossings : (∑ k ∈ Finset.range 168, newCrossings k) = 8 := by
  decide +kernel

theorem discriminant23_character_counts_at_twenty_of_band_conditions
    (h : Discriminant23TwentyBandConditions) :
    discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) = 22 ∧
      discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) = 22 := by
  have hStep (k : ℕ) (hk : k < 168) :
      discriminant23CharacterCountingFunction.HasStripZeroIncrement
        (discriminant23TwentyHeight k) (discriminant23TwentyHeight (k + 1)) (newCrossings k) := by
    have ha : 0 ≤ discriminant23TwentyHeight k := by unfold discriminant23TwentyHeight; positivity
    have hab : discriminant23TwentyHeight k < discriminant23TwentyHeight (k + 1) := by
      unfold discriminant23TwentyHeight
      push_cast
      linarith
    have he := h k hk
    dsimp only at he
    by_cases hd : discriminant23TwentyDirection k = 0
    · rw [ite_eq_left hd] at he
      rw [newCrossings, ite_eq_left hd]
      exact discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_ne_zero hab.le
        discriminant23_characterFold_one_sub he
    · rw [ite_eq_right hd] at he
      rw [newCrossings, ite_eq_right hd]
      exact discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_signed_crossing
        ha hab (by constructor <;> norm_num) discriminant23_characterFold_one_sub
        (fun t _ ↦ discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl)
        he.1 he.2.1 he.2.2.1 he.2.2.2
  have hCount := discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_mesh
    discriminant23TwentyHeight newCrossings 168 hStep
  rw [sum_newCrossings,
    show discriminant23TwentyHeight 0 = 19 / 2 by norm_num [discriminant23TwentyHeight],
    show discriminant23TwentyHeight 168 = 20 by norm_num [discriminant23TwentyHeight]] at hCount
  constructor
  · rw [hCount _ (fun _ _ ↦ trivial), discriminant23_character_counts_at_nineteen_halves.1]
  · rw [hCount _ (fun _ hLine ↦ hLine), discriminant23_character_counts_at_nineteen_halves.2]

theorem discriminant23_field_counts_at_twenty_add_forty_four_of_band_conditions
    (h : Discriminant23TwentyBandConditions) :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun _ ↦ True) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun _ ↦ True) + 44 ∧
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20
      (fun w ↦ w.re = 1 / 2) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun w ↦ w.re = 1 / 2) + 44 := by
  have hCount := discriminant23_character_counts_at_twenty_of_band_conditions h
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character, hCount.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character, hCount.2]

theorem discriminant23_dedekindRH_iff_character_above_twenty_of_band_conditions
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction)
    (h : Discriminant23TwentyBandConditions) :
    DedekindZetaRH Discriminant23GaloisField ↔ ∀ w : ℂ,
      1 / 2 < w.re → w.re ≤ 7 / 8 → 20 < w.im → discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_above_nineteen_halves_to_seven_eighths hD]
  constructor
  · intro hUpper w hlo hhi ht
    exact hUpper w hlo hhi (by linarith only [ht])
  · intro hUpper w hlo hhi ht hz
    by_cases hHigh : 20 < w.im
    · exact hUpper w hlo hhi hHigh hz
    · have hCounts := discriminant23_character_counts_at_twenty_of_band_conditions h
      have hLine := (discriminant23CharacterCountingFunction.stripCounts_equal_iff 20).mp
        (hCounts.1.trans hCounts.2.symm) w (by linarith only [hlo]) (by linarith only [hhi])
        (by rw [abs_of_nonneg (by linarith only [ht])]; exact le_of_not_gt hHigh) hz
      exact hlo.ne' hLine

#check Discriminant23TwentyBandConditions
#check @discriminant23_character_counts_at_twenty_of_band_conditions
#check @discriminant23_dedekindRH_iff_character_above_twenty_of_band_conditions
#print axioms discriminant23_twentyBandConditions_iff
#print axioms discriminant23_character_counts_at_twenty_of_band_conditions
#print axioms discriminant23_field_counts_at_twenty_add_forty_four_of_band_conditions
#print axioms discriminant23_dedekindRH_iff_character_above_twenty_of_band_conditions

end

end FieldTarget
