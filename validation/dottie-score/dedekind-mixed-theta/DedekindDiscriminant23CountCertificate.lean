import DedekindDiscriminant23ReadingCover
import DedekindDiscriminant23BelowCellSigns
import DedekindDiscriminant23SlopeCellSigns
import DedekindDiscriminant23AboveCellSigns

/-! The complete character count and its transfer to the field. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "L23" => Discriminant23GaloisField

/-- Through height 11/2, the complete and critical-line character counts are both two. -/
theorem discriminant23_character_counts_at_eleven_halves :
    discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) = 2 :=
  discriminant23_character_counts_of_integer_cells
    (discriminant23StoredReadingCoefficientBox false) (discriminant23StoredReadingCoefficientBox true)
    (discriminant23_storedReadingCoefficientBox_contains false)
    (discriminant23_storedReadingCoefficientBox_contains true)
    discriminant23_below_cell_signs discriminant23_slope_cell_signs discriminant23_above_cell_signs

/-- The squared character factor adds four to each quadratic-base count through height 11/2. -/
theorem discriminant23_field_counts_at_eleven_halves_add_four :
    (mixedThetaCountingFunction L23).stripZeroCount (11 / 2) (fun _ ↦ True) =
        (mixedThetaCountingFunction F23).stripZeroCount (11 / 2) (fun _ ↦ True) + 4 ∧
      (mixedThetaCountingFunction L23).stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) =
        (mixedThetaCountingFunction F23).stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) + 4 := by
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character,
      discriminant23_character_counts_at_eleven_halves.1]
  · rw [discriminant23_stripZeroCount_eq_base_add_character,
      discriminant23_character_counts_at_eleven_halves.2]

theorem discriminant23_character_zero_on_line_through_eleven_halves {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1) (hT : |w.im| ≤ 11 / 2)
    (hz : discriminant23CharacterFold w = 0) : w.re = 1 / 2 :=
  (discriminant23CharacterCountingFunction.stripCounts_equal_iff (11 / 2)).mp
    (discriminant23_character_counts_at_eleven_halves.1.trans
      discriminant23_character_counts_at_eleven_halves.2.symm) w hlo hhi hT hz

/-- Under the rational modulus-23 input, the remaining Dedekind RH target
begins above height 11/2. -/
theorem discriminant23_dedekindRH_iff_character_above_eleven_halves
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH L23 ↔ ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → 11 / 2 < |w.im| →
      discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_on_higher_right_strip hD]
  constructor
  · intro h w hre hhi hT
    exact h w hre hhi (by linarith only [hT])
  · intro h w hre hhi _ hz
    by_cases hT : |w.im| ≤ 11 / 2
    · exact (ne_of_gt hre) (discriminant23_character_zero_on_line_through_eleven_halves
        (by linarith only [hre]) hhi hT hz)
    · exact h w hre hhi (lt_of_not_ge hT) hz

#check @discriminant23_character_counts_at_eleven_halves
#check @discriminant23_field_counts_at_eleven_halves_add_four
#check @discriminant23_dedekindRH_iff_character_above_eleven_halves
#print axioms discriminant23_character_counts_at_eleven_halves
#print axioms discriminant23_field_counts_at_eleven_halves_add_four
#print axioms discriminant23_character_zero_on_line_through_eleven_halves
#print axioms discriminant23_dedekindRH_iff_character_above_eleven_halves

end

end FieldTarget

