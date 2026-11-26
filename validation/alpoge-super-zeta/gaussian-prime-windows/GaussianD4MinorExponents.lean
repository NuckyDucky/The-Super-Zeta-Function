import GaussianFrobeniusCentralIdeal
import GaussianD4MinorSupport

/-! Combine the exact local exponents with the two marked labels of
the dihedral closure. The unramified principal ideal is supplied as
the intersection of the conjugate primes. -/

namespace AlpogeSuperZeta

open UniqueFactorizationMonoid

noncomputable section

/-- If the local Frobenius lift commutes with the group action, its
residue congruence holds at every conjugate prime. -/
theorem frobenius_cast_dvd_of_conjugate_intersection {R G : Type*} [CommRing R] [Group G]
    (P : Ideal R) (ρ : G →* (R ≃+* R)) (g : G) (p : ℕ)
    (hCentral : ∀ γ : G, Commute γ g)
    (hIntersection : Ideal.span ({(p : R)} : Set R) = ⨅ γ : G, P.comap (ρ γ).toRingHom)
    (hFrob : ∀ a : R, Ideal.Quotient.mk P ((ρ g) a) = (Ideal.Quotient.mk P a) ^ p)
    (a : R) : (p : R) ∣ a ^ p - (ρ g) a := by
  apply Ideal.mem_span_singleton.mp
  rw [hIntersection, Ideal.mem_iInf]
  intro γ
  change (ρ γ) (a ^ p - (ρ g) a) ∈ P
  have hComm : (ρ γ) ((ρ g) a) = (ρ g) ((ρ γ) a) := by
    change ((ρ γ) * (ρ g)) a = ((ρ g) * (ρ γ)) a
    rw [← ρ.map_mul γ g, ← ρ.map_mul g γ, (hCentral γ).eq]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [map_sub, map_pow, hComm, hFrob, sub_self]

theorem gaussianCentral_commute_all (γ : GaussianClosureGroup) : Commute γ gaussianCentralElement := by
  change γ * gaussianCentralElement = gaussianCentralElement * γ
  revert γ
  decide +kernel

/-- At a retained unramified place the exact exponent is the floor
sum at the matching label and zero at the other labels. -/
theorem sqrtFrobeniusD4MinorIdeal_count {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)]
    (ρ : GaussianClosureGroup →* (R ≃+* R))
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} [CharP (R ⧸ P) p] (hp : p.Prime)
    (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (g label : GaussianClosureGroup) (hUnramified : (p : R) ∉ P ^ 2)
    (hIntersection : Ideal.span ({(p : R)} : Set R) =
      ⨅ γ : GaussianClosureGroup, P.comap (ρ γ).toRingHom)
    (hCard : Fintype.card (R ⧸ P) = p ^ orderOf g)
    (hStabilizer : ∀ h : GaussianClosureGroup, P.comap (ρ h).toRingHom = P ↔
      ∃ j : Fin 4, g ^ (j : ℕ) = h)
    (hFrob : ∀ a : R, Ideal.Quotient.mk P ((ρ g) a) = (Ideal.Quotient.mk P a) ^ p)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    (normalizedFactors (sqrtFrobeniusMinorIdeal x (ρ label).toRingHom)).count P =
      if g = label then frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p else 0 := by
  classical
  by_cases hMatch : g = label
  · rw [if_pos hMatch]
    subst g
    rcases hLabel with h | h
    · subst label
      rw [map_one]
      exact sqrtFrobeniusIdentityMinorIdeal_count P hx hp hLow hUnramified (by
        intro a
        have he := hFrob a
        rw [map_one] at he
        exact he)
    · subst label
      have hOrder : 2 ≤ orderOf gaussianCentralElement := by
        have hz : gaussianCentralElement ≠ 1 := by decide +kernel
        have hPos := orderOf_pos gaussianCentralElement
        have hNe : orderOf gaussianCentralElement ≠ 1 := fun he => hz (orderOf_eq_one_iff.mp he)
        omega
      have hPCard : p ^ 2 ≤ Fintype.card (R ⧸ P) := by
        rw [hCard]
        exact Nat.pow_le_pow_right hp.pos hOrder
      exact sqrtFrobeniusMinorIdeal_count_of_normalized_values P (ρ gaussianCentralElement) hx hp
        hLow hUnramified hPCard
        (frobenius_cast_dvd_of_conjugate_intersection P ρ gaussianCentralElement p
          gaussianCentral_commute_all hIntersection hFrob)
  · rw [if_neg hMatch]
    apply Ideal.count_normalizedFactors_eq (n := 0)
    · simp
    · rw [zero_add, pow_one]
      exact fun hLe => hMatch (sqrtFrobeniusMinorIdeal_only_matching_label P ρ hx hLow g label
        hCard hStabilizer hFrob hLabel hLe)

#print axioms frobenius_cast_dvd_of_conjugate_intersection
#print axioms gaussianCentral_commute_all
#print axioms sqrtFrobeniusD4MinorIdeal_count

end

end AlpogeSuperZeta
