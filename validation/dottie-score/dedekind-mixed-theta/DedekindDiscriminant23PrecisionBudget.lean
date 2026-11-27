import DedekindDiscriminant23AdaptiveParameters

namespace FieldTarget

private theorem discriminant23_phaseTermCount_at_1641_le :
    discriminant23PhaseTermCount 1641 ≤ 14450 := by
  have hBox (Q : ℤ → ℤ → ℤ) : (characterThetaTermsUpTo Q 1641).card ≤ 7225 := by
    unfold characterThetaTermsUpTo
    exact (Finset.card_filter_le _ _).trans (by decide +kernel)
  unfold discriminant23PhaseTermCount
  exact Nat.add_le_add (hBox _) (hBox _)

/-- An explicit value and slope error budget from the integer parameter tests.
The forty-eight panels use the exact exponential phase on each panel. -/
theorem discriminant23_phase_error_below_10_pow_neg_666 {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo 1641 12 2238 false w‖ <
      1 / (10 : ℝ) ^ 666 ∧
    ‖deriv discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo 1641 12 2238 true w‖ <
      1 / (10 : ℝ) ^ 666 := by
  have hCutoff : discriminant23NormCutoff 1184 = 1641 := by decide +kernel
  have hQuad :
      12 * (10 ^ 666 : ℕ) * 12 * (12 + 1) *
        discriminant23PhaseTermCount (discriminant23NormCutoff 1184) < 1 * 2 ^ 2238 := by
    rw [hCutoff]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ discriminant23_phaseTermCount_at_1641_le)
      (by decide +kernel)
  have h := discriminant23_phaseError_lt_of_integer_bounds
    (a := 1) (b := 10 ^ 666) (k := 1184) (L := 12) (depth := 2238)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hQuad hlo hhi
  simpa only [hCutoff, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using h

#check @discriminant23_phase_error_below_10_pow_neg_666
#print axioms discriminant23_phase_error_below_10_pow_neg_666

end FieldTarget
