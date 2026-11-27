import DedekindDiscriminant23NineteenHalvesBand
import DedekindSevenEighthsCoverage

namespace FieldTarget

open ArtinPrimitiveRootsConjecture

local notation "L23" => Discriminant23GaloisField
local notation "F23" => (discriminant23QuadraticSubfield : Type)

theorem discriminant23_character_ne_zero_above_seven_eighths {w : ℂ}
    (hlo : 7 / 8 < w.re) (hhi : w.re < 1) : discriminant23CharacterFold w ≠ 0 := by
  intro hz
  have h₀ : 0 < w.re := by linarith only [hlo]
  exact mixedThetaContinuation_ne_zero_above_seven_eighths L23 hlo hhi
    ((discriminant23_dedekind_zero_iff_base_or_character w h₀ hhi).mpr (.inr hz))

theorem discriminant23_dedekindRH_iff_character_above_nineteen_halves_to_seven_eighths
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH L23 ↔ ∀ w : ℂ,
      1 / 2 < w.re → w.re ≤ 7 / 8 → 19 / 2 < w.im → discriminant23CharacterFold w ≠ 0 := by
  have hF := dedekindZetaRH_of_cyclotomic_embedding 23 F23 discriminant23_cyclotomicEmbedding hD
  constructor
  · intro hL w hlo hhi _ hz
    have h₀ : 0 < w.re := by linarith only [hlo]
    have h₁ : w.re < 1 := by linarith only [hhi]
    have hZ := (discriminant23_dedekind_zero_iff_base_or_character w h₀ h₁).mpr (.inr hz)
    exact hlo.ne' (hL (mixedThetaContinuation L23) (mixedThetaContinuation_isDedekind L23) w h₀ h₁ hZ)
  · intro h
    apply (dedekindZetaRH_iff_seven_eighths_nonnegative_band L23).mpr
    intro w hlo hhi him hz
    have h₀ : 0 < w.re := by linarith only [hlo]
    have h₁ : w.re < 1 := by linarith only [hhi]
    rcases (discriminant23_dedekind_zero_iff_base_or_character w h₀ h₁).mp hz with hb | hc
    · exact hlo.ne' (hF (mixedThetaContinuation F23) (mixedThetaContinuation_isDedekind F23) w h₀ h₁ hb)
    · by_cases ht : 19 / 2 < w.im
      · exact h w hlo hhi ht hc
      · have ht' : |w.im| ≤ 19 / 2 := by simpa only [abs_of_nonneg him] using le_of_not_gt ht
        have hCount := discriminant23_character_counts_at_nineteen_halves
        have hLine := (discriminant23CharacterCountingFunction.stripCounts_equal_iff (19 / 2)).mp
          (hCount.1.trans hCount.2.symm) w h₀ h₁ ht' hc
        exact hlo.ne' hLine

#check @discriminant23_character_ne_zero_above_seven_eighths
#check @discriminant23_dedekindRH_iff_character_above_nineteen_halves_to_seven_eighths
#print axioms discriminant23_character_ne_zero_above_seven_eighths
#print axioms discriminant23_dedekindRH_iff_character_above_nineteen_halves_to_seven_eighths

end FieldTarget
