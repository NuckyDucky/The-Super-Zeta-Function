import DedekindDiscriminant23GaussPilotArithmetic
import ComplexStripBracketLowerCount
import DedekindDiscriminant23NineteenHalvesBand

/-! The value at height twenty and the two endpoints of the first new crossing. -/

namespace FieldTarget

open Set

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem phase_at_twenty : ∀ j i, gauss23PhaseCheck 320 16 j i = true := by
  decide +kernel

theorem discriminant23_gauss_re_neg_at_twenty :
    (discriminant23CharacterFold ⟨1 / 2, 20⟩).re < 0 := by
  have h := gauss23_critical_sign_of_check 320 (d := 16) (by norm_num) false
    (by norm_num) phase_at_twenty gauss23_twenty_clearsError
  norm_num [gauss23CriticalPoint] at h ⊢
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem phase_at_first_crossing (hi : Bool) :
    ∀ j i, gauss23PhaseCheck (if hi then 165 else 164) 16 j i = true := by
  cases hi <;> decide +kernel

theorem discriminant23_gauss_first_crossing_signs :
    (discriminant23CharacterFold ⟨1 / 2, 41 / 4⟩).re < 0 ∧
      0 < (discriminant23CharacterFold ⟨1 / 2, 165 / 16⟩).re := by
  constructor
  · have h := gauss23_critical_sign_of_check 164 (d := 16) (by norm_num) false
      (by norm_num) (phase_at_first_crossing false) gauss23_firstLower_clearsError
    norm_num [gauss23CriticalPoint] at h ⊢
    exact h
  · have h := gauss23_critical_sign_of_check 165 (d := 16) (by norm_num) true
      (by norm_num) (phase_at_first_crossing true) gauss23_firstUpper_clearsError
    norm_num [gauss23CriticalPoint] at h ⊢
    exact h

theorem discriminant23_gauss_first_crossing_exists :
    ∃ t ∈ Ioo (41 / 4 : ℝ) (165 / 16), discriminant23CharacterFold ⟨1 / 2, t⟩ = 0 := by
  let f (t : ℝ) := (discriminant23CharacterFold ⟨1 / 2, t⟩).re
  have hcont : Continuous f := by
    have hPoint : Continuous (fun t : ℝ ↦ (⟨1 / 2, t⟩ : ℂ)) := by
      convert (continuous_const.add (Complex.continuous_ofReal.mul continuous_const) :
        Continuous fun t : ℝ ↦ (1 / 2 : ℂ) + (t : ℂ) * Complex.I) using 1
      funext t
      apply Complex.ext <;> simp
    exact Complex.continuous_re.comp (discriminant23CharacterFold_differentiable.continuous.comp hPoint)
  have h := discriminant23_gauss_first_crossing_signs
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo (by norm_num : (41 / 4 : ℝ) ≤ 165 / 16)
    hcont.continuousOn (show (0 : ℝ) ∈ Ioo (f (41 / 4)) (f (165 / 16)) from ⟨h.1, h.2⟩)
  exact ⟨t, ht, Complex.ext hzero (discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl)⟩

theorem discriminant23_gauss_character_counts_at_twenty_ge_eight :
    8 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) ∧
      8 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) := by
  have hadd (P : ℂ → Prop) (hP : ∀ w : ℂ, w.re = 1 / 2 → P w) :=
    discriminant23CharacterCountingFunction.stripZeroCount_ge_of_disjoint_brackets
      (ι := Fin 1) (T := 19 / 2) (U := 20) (by norm_num) (by norm_num)
      (fun _ ↦ 41 / 4) (fun _ ↦ 165 / 16) (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
      (fun i j h ↦ (h (Subsingleton.elim i j)).elim)
      (fun _ ↦ discriminant23_gauss_first_crossing_exists) discriminant23_characterFold_one_sub P hP
  constructor
  · have h := hadd (fun _ ↦ True) (fun _ _ ↦ trivial)
    norm_num [discriminant23_character_counts_at_nineteen_halves.1] at h
    exact h
  · have h := hadd (fun w ↦ w.re = 1 / 2) (fun _ h ↦ h)
    norm_num [discriminant23_character_counts_at_nineteen_halves.2] at h
    exact h

theorem discriminant23_gauss_field_counts_at_twenty_ge_base_add_sixteen :
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun _ ↦ True) + 16 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun _ ↦ True) ∧
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun w ↦ w.re = 1 / 2) + 16 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun w ↦ w.re = 1 / 2) := by
  obtain ⟨hFull, hLine⟩ := discriminant23_gauss_character_counts_at_twenty_ge_eight
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character]
    omega
  · rw [discriminant23_stripZeroCount_eq_base_add_character]
    omega

#print axioms discriminant23_gauss_re_neg_at_twenty
#print axioms discriminant23_gauss_first_crossing_signs
#print axioms discriminant23_gauss_first_crossing_exists
#print axioms discriminant23_gauss_character_counts_at_twenty_ge_eight
#print axioms discriminant23_gauss_field_counts_at_twenty_ge_base_add_sixteen

end FieldTarget
