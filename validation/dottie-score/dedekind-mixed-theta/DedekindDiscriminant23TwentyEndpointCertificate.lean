import Gauss23TwentyEndpointTransfer
import Gauss23TwentyEndpointsA
import Gauss23TwentyEndpointsB
import DedekindDiscriminant23GaussPilotArithmetic
import Mathlib.Tactic.FinCases

/-! The directed endpoint passes and their unconditional lower counts. -/

namespace FieldTarget

set_option maxRecDepth 8192 in
theorem discriminant23_twentyEndpointSigns : Discriminant23TwentyEndpointSigns := by
  apply discriminant23_twentyEndpointSigns_of_marked
  intro i
  fin_cases i
  · exact discriminant23_signed_endpoints_of_clearances 12 (by decide) (by decide)
      gauss23_firstLower_clearsError gauss23_firstUpper_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 30 (by decide) (by decide)
      gauss23_at_182_clearsError gauss23_at_183_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 54 (by decide) (by decide)
      gauss23_at_206_clearsError gauss23_at_207_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 82 (by decide) (by decide)
      gauss23_at_234_clearsError gauss23_at_235_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 111 (by decide) (by decide)
      gauss23_at_263_clearsError gauss23_at_264_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 121 (by decide) (by decide)
      gauss23_at_273_clearsError gauss23_at_274_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 137 (by decide) (by decide)
      gauss23_at_289_clearsError gauss23_at_290_clearsError
  · exact discriminant23_signed_endpoints_of_clearances 153 (by decide) (by decide)
      gauss23_at_305_clearsError gauss23_at_306_clearsError

theorem discriminant23_twenty_character_counts_ge :
    22 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) ∧
      22 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) :=
  discriminant23_twenty_character_counts_ge_of_endpointSigns discriminant23_twentyEndpointSigns

theorem discriminant23_twenty_character_counts_eq_iff_total_le :
    (discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) = 22 ∧
      discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) = 22) ↔
      discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) ≤ 22 := by
  constructor
  · exact fun h ↦ h.1.le
  · intro h
    have hMono (P Q : ℂ → Prop) (hPQ : ∀ w, P w → Q w) :
        discriminant23CharacterCountingFunction.stripZeroCount 20 P ≤
          discriminant23CharacterCountingFunction.stripZeroCount 20 Q := by
      classical
      unfold NonzeroEntireFunction.stripZeroCount
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro w hw
        obtain ⟨hz, hp⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨hz, hPQ w hp⟩
      · exact fun _ _ _ ↦ Nat.zero_le _
    have hLineLe := hMono (fun w ↦ w.re = 1 / 2) (fun _ ↦ True) (fun _ _ ↦ trivial)
    exact ⟨le_antisymm h discriminant23_twenty_character_counts_ge.1,
      le_antisymm (hLineLe.trans h) discriminant23_twenty_character_counts_ge.2⟩

theorem discriminant23_twenty_field_counts_ge :
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun _ ↦ True) + 44 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun _ ↦ True) ∧
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun w ↦ w.re = 1 / 2) + 44 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun w ↦ w.re = 1 / 2) :=
  discriminant23_twenty_field_counts_ge_of_endpointSigns discriminant23_twentyEndpointSigns

#print axioms discriminant23_twentyEndpointSigns
#print axioms discriminant23_twenty_character_counts_ge
#print axioms discriminant23_twenty_character_counts_eq_iff_total_le
#print axioms discriminant23_twenty_field_counts_ge

end FieldTarget
