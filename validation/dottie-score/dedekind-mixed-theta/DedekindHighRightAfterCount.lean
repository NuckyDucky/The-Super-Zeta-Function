import DedekindDiscriminant23CountCertificate
import DedekindMixedThetaRightEdge

/-! A complete count through a fixed height and the right-edge theorem
restrict all further zero exclusion to the interior of the right half-strip. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped ComplexConjugate

noncomputable section

/-- A signed or otherwise certified next band extends both complete counts
without replaying the lower band. -/
theorem dedekind_stripCounts_equal_of_high_right_band
    (K : Type) [Field K] [NumberField K] {T U : ℝ}
    (hcount : (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2))
    (hband : ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → T < |w.im| → |w.im| ≤ U →
      mixedThetaContinuation K w ≠ 0) :
    (mixedThetaCountingFunction K).stripZeroCount U (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount U (fun w ↦ w.re = 1 / 2) := by
  apply ((mixedThetaCountingFunction K).stripCounts_equal_iff U).mpr
  intro w hlo hhi him hreading
  by_cases hT : |w.im| ≤ T
  · exact ((mixedThetaCountingFunction K).stripCounts_equal_iff T).mp hcount w hlo hhi hT hreading
  have hz := (mixedThetaEntireReading_zero_iff K w hlo hhi).mp hreading
  have noRight (v : ℂ) (hre : 1 / 2 < v.re) (hvhi : v.re < 1) (hvt : T < |v.im|)
      (hvU : |v.im| ≤ U) : mixedThetaContinuation K v ≠ 0 := by
    by_cases hedge : v.re ≤ 31 / 32
    · exact hband v hre hedge hvt hvU
    have hv1 : v ≠ 1 := by rintro rfl; norm_num at hvhi
    exact mixedThetaContinuation_ne_zero_above_31_32 K (lt_of_not_ge hedge) hv1
  rcases lt_trichotomy w.re (1 / 2) with hl | heq | hr
  · have hre : (1 - conj w).re = 1 - w.re := by simp [Complex.sub_re]
    have him' : (1 - conj w).im = w.im := by simp [Complex.sub_im]
    exact (noRight (1 - conj w) (by rw [hre]; linarith only [hl])
      (by rw [hre]; linarith only [hlo]) (by rw [him']; exact lt_of_not_ge hT)
      (by rw [him']; exact him) (mixedThetaContinuation_reflects K w hlo hhi hz)).elim
  · exact heq
  · exact (noRight w hr hhi (lt_of_not_ge hT) him hz).elim

theorem dedekindZetaRH_iff_high_right_of_strip_counts
    (K : Type) [Field K] [NumberField K] {T : ℝ}
    (hcount : (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2)) :
    DedekindZetaRH K ↔ ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → T < |w.im| →
      mixedThetaContinuation K w ≠ 0 := by
  constructor
  · intro h w hre hhi _ hz
    have hLine := (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind K)).mp h
    exact (ne_of_gt hre) (hLine w (by linarith only [hre]) (by linarith only [hhi]) hz)
  · intro h
    apply (dedekindZetaRH_iff_cofinal_mixedTheta_counts K).mpr
    intro H
    exact ⟨H, le_rfl, dedekind_stripCounts_equal_of_high_right_band K hcount
      (fun w hlo hhi ht _ ↦ h w hlo hhi ht)⟩

/-- The right edge can also be removed from the remaining character problem. -/
theorem discriminant23_dedekindRH_iff_character_high_right
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH Discriminant23GaloisField ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → 11 / 2 < |w.im| →
        discriminant23CharacterFold w ≠ 0 := by
  rw [discriminant23_dedekindRH_iff_character_above_eleven_halves hD]
  constructor
  · intro h w hre hhi ht
    exact h w hre (by linarith only [hhi]) ht
  · intro h w hre hhi ht hz
    by_cases hedge : w.re ≤ 31 / 32
    · exact h w hre hedge ht hz
    have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
    exact mixedThetaContinuation_ne_zero_above_31_32 Discriminant23GaloisField
      (lt_of_not_ge hedge) hw1
      ((discriminant23_dedekind_zero_iff_base_or_character w (by linarith only [hre]) hhi).mpr
        (.inr hz))

#check @dedekind_stripCounts_equal_of_high_right_band
#check @dedekindZetaRH_iff_high_right_of_strip_counts
#check @discriminant23_dedekindRH_iff_character_high_right
#print axioms dedekind_stripCounts_equal_of_high_right_band
#print axioms dedekindZetaRH_iff_high_right_of_strip_counts
#print axioms discriminant23_dedekindRH_iff_character_high_right

end

end FieldTarget
