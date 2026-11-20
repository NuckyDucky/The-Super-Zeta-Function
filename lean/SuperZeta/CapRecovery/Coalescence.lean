import SuperZeta.CapRecovery.HiddenLift
import SuperZeta.CapRecovery.OrientationMark

/-! Joint recovery of the signed lift and the chronological word from an
observed cap curvature and independently attributed inert-prime readings. -/
noncomputable section
namespace SuperZeta.Coalescence

open SignWords Resonant OrientationMark

/-- For a known nonzero weight, the first labeled prime reading selects the
unique signed lift and word on the curvature fiber. -/
theorem first_reading_iff {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    {u v : List Sign} (hu : u ≠ []) (hv : v ≠ []) {a : ℝ} (ha : a ≠ 0) :
    (curvature m u = curvature n v ∧ reading a u 1 = reading a v 1) ↔
      n = m ∧ v = u := by
  constructor
  · rintro ⟨hK, h₁⟩
    rcases (HiddenLift.curvature_eq_iff hm hn hu hv).mp hK with h | ⟨_, rfl⟩
    · exact h
    · exact (odd_reading_ne ha u (List.length_pos_iff.mpr hu) (by decide : Odd 1) h₁).elim
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- The normalized detector reads the actual quadratic character modulo
three at two. Its first coefficient selects the signed lift and word. -/
theorem dyadic_first_reading_iff {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    {u v : List Sign} (hu : u ≠ []) (hv : v ≠ []) :
    (curvature m u = curvature n v ∧
      FieldWeights.primePowerWeight (1/7) (legendreSym 3 2 : ℝ)
          (DyadicWeights.exponent (u.take 1)) =
        FieldWeights.primePowerWeight (1/7) (legendreSym 3 2 : ℝ)
          (DyadicWeights.exponent (v.take 1))) ↔ n = m ∧ v = u := by
  simpa only [reading, DyadicWeights.legendre_three_two, Int.cast_neg, Int.cast_one]
    using first_reading_iff hm hn hu hv (a := 1/7) (by norm_num)

/-- When the signed weight is unknown, a length-two prefix suffices. Equality
of curvature and both labeled coefficients forces equality of all three unknowns. -/
theorem two_readings_iff {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    {u v : List Sign} (hu : 2 ≤ u.length) (hv : 2 ≤ v.length)
    {a b : ℝ} (ha : a ≠ 0) :
    (curvature m u = curvature n v ∧ reading a u 1 = reading b v 1 ∧
        reading a u 2 = reading b v 2) ↔ n = m ∧ v = u ∧ b = a := by
  constructor
  · rintro ⟨hK, h₁, h₂⟩
    have hu' : u ≠ [] := List.length_pos_iff.mp (by omega)
    have hv' : v ≠ [] := List.length_pos_iff.mp (by omega)
    rcases (HiddenLift.curvature_eq_iff hm hn hu' hv').mp hK with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨rfl, rfl, by rw [← recover_weight a v 1, ← recover_weight b v 1, h₁]⟩
    · have hz := (even_odd_calibration a b u hu (by omega : 1 ≤ u.length)
          (by decide : Even 2) (by decide : Odd 1)).mp ⟨h₂, h₁⟩
      exact (ha hz.1).elim
  · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩

end SuperZeta.Coalescence
