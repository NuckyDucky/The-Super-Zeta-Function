import GaussianFrobeniusMinorIdeal
import GaussianCMPrimeBarrier
import Mathlib.GroupTheory.OrderOfElement

/-! Pass from residue separation to the identity and central labels of
the quartic's dihedral normal closure. The hypotheses name the action,
residue cardinality, and Frobenius of the chosen unramified place. -/

namespace AlpogeSuperZeta

theorem gaussianD4_pow_four (g : GaussianClosureGroup) : g ^ 4 = 1 := by
  revert g
  decide +kernel

theorem gaussianCentral_frobenius_power_cases (g : GaussianClosureGroup) :
    g ≠ gaussianCentralElement →
      (∀ j : Fin 4, g ^ (j : ℕ) ≠ gaussianCentralElement) ∨ g ^ 2 = gaussianCentralElement := by
  revert g
  decide +kernel

private theorem gaussianD4_order_of_central_square {g : GaussianClosureGroup}
    (h : g ^ 2 = gaussianCentralElement) : orderOf g = 4 := by
  have hz : gaussianCentralElement ≠ 1 := by decide +kernel
  have hd := orderOf_dvd_of_pow_eq_one (gaussianD4_pow_four g)
  have hUpper := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hLower := orderOf_pos g
  have h₁ : orderOf g ≠ 1 := fun h₁ => by
    have hg := orderOf_eq_one_iff.mp h₁
    exact hz (h.symm.trans (by simp [hg]))
  have h₂ : orderOf g ≠ 2 := fun h₂ => by
    have he := pow_orderOf_eq_one g
    rw [h₂, h] at he
    exact hz he
  have h₃ : orderOf g ≠ 3 := fun h₃ => by
    rw [h₃] at hd
    norm_num at hd
  omega

private theorem gaussianCentral_order : orderOf gaussianCentralElement = 2 := by
  have hz : gaussianCentralElement ≠ 1 := by decide +kernel
  have hd := orderOf_dvd_of_pow_eq_one (by decide +kernel : gaussianCentralElement ^ 2 = 1)
  have hUpper := Nat.le_of_dvd (by decide : 0 < 2) hd
  have hLower := orderOf_pos gaussianCentralElement
  have h₁ : orderOf gaussianCentralElement ≠ 1 := fun e => hz (orderOf_eq_one_iff.mp e)
  omega

/-- With the unramified residue action supplied, an eligible prime can
divide the common Hasse-minor ideal only at its own marked label. -/
theorem sqrtFrobeniusMinorIdeal_only_matching_label {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)]
    (ρ : GaussianClosureGroup →* (R ≃+* R))
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (g label : GaussianClosureGroup)
    (hCard : Fintype.card (R ⧸ P) = p ^ orderOf g)
    (hStabilizer : ∀ h : GaussianClosureGroup, P.comap (ρ h).toRingHom = P ↔
      ∃ j : Fin 4, g ^ (j : ℕ) = h)
    (hFrobenius : ∀ a : R, Ideal.Quotient.mk P ((ρ g) a) = (Ideal.Quotient.mk P a) ^ p)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    sqrtFrobeniusMinorIdeal x (ρ label).toRingHom ≤ P → g = label := by
  classical
  have hp₀ : 0 < p := Nat.cast_pos.mp ((by dsimp [gaussianSqrtTriangleScale]; positivity :
    0 < gaussianSqrtTriangleScale x).trans_le hp)
  intro hDiv
  by_contra hMismatch
  rcases hLabel with hl | hl
  · subst label
    have hOrder : 2 ≤ orderOf g := by
      have hOrd := orderOf_pos g
      have hNe : orderOf g ≠ 1 := fun hh => hMismatch (orderOf_eq_one_iff.mp hh)
      omega
    have hSize : p ^ 2 ≤ Fintype.card (R ⧸ P) := by
      rw [hCard]
      exact Nat.pow_le_pow_right hp₀ hOrder
    have hRange := (sqrtFrobeniusScale_prime_bounds hx hp).1.trans (Nat.cast_le.mpr hSize)
    exact (sqrtFrobeniusMinorIdeal_not_le_of_diagonal P (ρ 1).toRingHom hx hRange (fun a => by
      rw [map_one]
      rfl)) hDiv
  · subst label
    rcases gaussianCentral_frobenius_power_cases g hMismatch with hOut | hSquare
    · have hMove : P.comap (ρ gaussianCentralElement).toRingHom ≠ P := fun hh => by
        obtain ⟨j, hj⟩ := (hStabilizer gaussianCentralElement).mp hh
        exact hOut j hj
      have hSize : p ≤ Fintype.card (R ⧸ P) := by
        rw [hCard, ← pow_one p]
        simpa only [pow_one] using
          Nat.pow_le_pow_right hp₀ (show 1 ≤ orderOf g from orderOf_pos g)
      exact (sqrtFrobeniusMinorIdeal_not_le_of_comap_ne P (ρ gaussianCentralElement) hx hp hSize hMove) hDiv
    · have hSize : p ^ 4 ≤ Fintype.card (R ⧸ P) := by
        rw [hCard, gaussianD4_order_of_central_square hSquare]
      have hSquaredFrob (a : R) :
          Ideal.Quotient.mk P ((ρ gaussianCentralElement).toRingHom a) = (Ideal.Quotient.mk P a) ^ (p ^ 2) := by
        rw [← hSquare, map_pow, pow_two]
        change Ideal.Quotient.mk P ((ρ g) ((ρ g) a)) = (Ideal.Quotient.mk P a) ^ (p ^ 2)
        rw [hFrobenius, hFrobenius, ← pow_mul, pow_two]
      exact (sqrtFrobeniusMinorIdeal_not_le_of_powerGraph P (ρ gaussianCentralElement).toRingHom hx hp
        hSize hSquaredFrob) hDiv

/-- Exact support at retained unramified primes. The upper endpoint
is excluded as well as every different Frobenius label. -/
theorem sqrtFrobeniusMinorIdeal_le_iff_matching_window {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)]
    (ρ : GaussianClosureGroup →* (R ≃+* R))
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} [CharP (R ⧸ P) p] (hp : p.Prime)
    (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (g label : GaussianClosureGroup)
    (hCard : Fintype.card (R ⧸ P) = p ^ orderOf g)
    (hStabilizer : ∀ h : GaussianClosureGroup, P.comap (ρ h).toRingHom = P ↔
      ∃ j : Fin 4, g ^ (j : ℕ) = h)
    (hFrobenius : ∀ a : R, Ideal.Quotient.mk P ((ρ g) a) = (Ideal.Quotient.mk P a) ^ p)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    sqrtFrobeniusMinorIdeal x (ρ label).toRingHom ≤ P ↔ (p : ℝ) < x ∧ g = label := by
  constructor
  · intro hDiv
    have hMatch := sqrtFrobeniusMinorIdeal_only_matching_label P ρ hx hLow g label
      hCard hStabilizer hFrobenius hLabel hDiv
    refine ⟨?_, hMatch⟩
    by_contra! hPast
    subst g
    rcases hLabel with hl | hl
    · subst label
      have hSize : x ≤ (Fintype.card (R ⧸ P) : ℝ) := by
        simpa [hCard, orderOf_one] using hPast
      exact (sqrtFrobeniusMinorIdeal_not_le_of_diagonal P (ρ 1).toRingHom hx hSize (fun a => by
        rw [map_one]
        rfl)) hDiv
    · subst label
      have hSize : p ^ 2 ≤ Fintype.card (R ⧸ P) := by rw [hCard, gaussianCentral_order]
      exact (sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_at_upper_cutoff P
        (ρ gaussianCentralElement).toRingHom hx hLow hPast hSize hFrobenius) hDiv
  · rintro ⟨hHigh, hMatch⟩
    subst label
    exact sqrtFrobeniusMinorIdeal_le_of_frobenius P (ρ g).toRingHom hx hp hLow hHigh hFrobenius

#print axioms gaussianD4_pow_four
#print axioms sqrtFrobeniusMinorIdeal_le_iff_matching_window
#print axioms gaussianCentral_frobenius_power_cases
#print axioms sqrtFrobeniusMinorIdeal_only_matching_label

end AlpogeSuperZeta
