import Gauss23Height10Values
import Gauss23Height10Cover
import Gauss23Height11Values
import Gauss23Height11Cover
import Gauss23Height12Values
import Gauss23Height12Cover
import Gauss23Height13Values
import Gauss23Height13Cover
import Gauss23Height14Values
import Gauss23Height14Cover
import Gauss23Height15Values
import Gauss23Height15Cover
import Gauss23Height16Values
import Gauss23Height16Cover
import Gauss23Height17Values
import Gauss23Height17Cover
import Gauss23Height18Values
import Gauss23Height18Cover
import Gauss23Height19Values
import Gauss23Height19Cover
import Gauss23Height20Values
import Gauss23Height20Cover
import DedekindDiscriminant23TwentyEndpointCertificate

/-! The exact counts through height 20, using the kernel-checked rectangle cover. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture

private theorem cellsFromAnchor (a : Fin 11) :
    ∀ j : Fin (if a.val = 10 then 8 else 16),
      Discriminant23TwentyCellCondition (16 * a.val + j.val) := by
  fin_cases a
  · exact gauss23_twentySegment_of_checks 0 16 10 (by decide +kernel) (gauss23TwentyValue 10)
      gauss23_values_at_10_contain (by decide +kernel) gauss23_checks_at_10
  · exact gauss23_twentySegment_of_checks 16 16 11 (by decide +kernel) (gauss23TwentyValue 11)
      gauss23_values_at_11_contain (by decide +kernel) gauss23_checks_at_11
  · exact gauss23_twentySegment_of_checks 32 16 12 (by decide +kernel) (gauss23TwentyValue 12)
      gauss23_values_at_12_contain (by decide +kernel) gauss23_checks_at_12
  · exact gauss23_twentySegment_of_checks 48 16 13 (by decide +kernel) (gauss23TwentyValue 13)
      gauss23_values_at_13_contain (by decide +kernel) gauss23_checks_at_13
  · exact gauss23_twentySegment_of_checks 64 16 14 (by decide +kernel) (gauss23TwentyValue 14)
      gauss23_values_at_14_contain (by decide +kernel) gauss23_checks_at_14
  · exact gauss23_twentySegment_of_checks 80 16 15 (by decide +kernel) (gauss23TwentyValue 15)
      gauss23_values_at_15_contain (by decide +kernel) gauss23_checks_at_15
  · exact gauss23_twentySegment_of_checks 96 16 16 (by decide +kernel) (gauss23TwentyValue 16)
      gauss23_values_at_16_contain (by decide +kernel) gauss23_checks_at_16
  · exact gauss23_twentySegment_of_checks 112 16 17 (by decide +kernel) (gauss23TwentyValue 17)
      gauss23_values_at_17_contain (by decide +kernel) gauss23_checks_at_17
  · exact gauss23_twentySegment_of_checks 128 16 18 (by decide +kernel) (gauss23TwentyValue 18)
      gauss23_values_at_18_contain (by decide +kernel) gauss23_checks_at_18
  · exact gauss23_twentySegment_of_checks 144 16 19 (by decide +kernel) (gauss23TwentyValue 19)
      gauss23_values_at_19_contain (by decide +kernel) gauss23_checks_at_19
  · exact gauss23_twentySegment_of_checks 160 8 20 (by decide +kernel) (gauss23TwentyValue 20)
      gauss23_values_at_20_contain (by decide +kernel) gauss23_checks_at_20

theorem discriminant23_twentyCellConditions : Discriminant23TwentyCellConditions := by
  intro k hk
  let a : Fin 11 := ⟨k / 16, by omega⟩
  let j : Fin (if a.val = 10 then 8 else 16) :=
    ⟨k % 16, by dsimp only [a]; split_ifs <;> omega⟩
  have h : 16 * a.val + j.val = k := by
    change 16 * (k / 16) + k % 16 = k
    omega
  exact h ▸ cellsFromAnchor a j

theorem discriminant23_twentyBandConditions : Discriminant23TwentyBandConditions :=
  discriminant23_twentyBandConditions_iff.mpr
    ⟨discriminant23_twentyEndpointSigns, discriminant23_twentyCellConditions⟩

theorem discriminant23_character_counts_at_twenty :
    discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) = 22 ∧
      discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) = 22 :=
  discriminant23_character_counts_at_twenty_of_band_conditions discriminant23_twentyBandConditions

theorem discriminant23_character_line_through_twenty {w : ℂ}
    (hx₀ : 0 < w.re) (hx₁ : w.re < 1) (hy : |w.im| ≤ 20)
    (hz : discriminant23CharacterFold w = 0) : w.re = 1 / 2 := by
  have hCount := discriminant23_character_counts_at_twenty
  exact (discriminant23CharacterCountingFunction.stripCounts_equal_iff 20).mp
    (hCount.1.trans hCount.2.symm) w hx₀ hx₁ hy hz

theorem discriminant23_field_counts_at_twenty_add_forty_four :
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun _ ↦ True) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun _ ↦ True) + 44 ∧
    (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20
      (fun w ↦ w.re = 1 / 2) =
      (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun w ↦ w.re = 1 / 2) + 44 :=
  discriminant23_field_counts_at_twenty_add_forty_four_of_band_conditions discriminant23_twentyBandConditions

theorem discriminant23_dedekindRH_iff_character_above_twenty
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔ ∀ w : ℂ,
      1 / 2 < w.re → w.re ≤ 7 / 8 → 20 < w.im → discriminant23CharacterFold w ≠ 0 :=
  discriminant23_dedekindRH_iff_character_above_twenty_of_band_conditions hD
    discriminant23_twentyBandConditions

#check @discriminant23_character_counts_at_twenty
#check @discriminant23_field_counts_at_twenty_add_forty_four
#check @discriminant23_dedekindRH_iff_character_above_twenty
#print axioms discriminant23_twentyCellConditions
#print axioms discriminant23_twentyBandConditions
#print axioms discriminant23_character_counts_at_twenty
#print axioms discriminant23_character_line_through_twenty
#print axioms discriminant23_field_counts_at_twenty_add_forty_four
#print axioms discriminant23_dedekindRH_iff_character_above_twenty

end FieldTarget
