import DedekindCyclicSubgroupWeights
import DedekindPrimeFiberCounting

namespace FieldTarget

open scoped NumberField BigOperators Classical
open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The logarithmic Euler coefficient at the n-th power of a base prime,
with the common log of the base norm omitted. -/
noncomputable def primePowerResidueCount (E : IntermediateField K L)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) : ℤ :=
  ∑ Q : p.asIdeal.primesOver (𝓞 E),
    if Q.val.inertiaDeg (𝓞 K) ∣ n then (Q.val.inertiaDeg (𝓞 K) : ℤ) else 0

/-- One family of integer weights recovers every unramified base-prime
logarithmic Euler coefficient from cyclic fixed fields. -/
theorem exists_weighted_unramified_prime_power_match [IsGalois K L] :
    ∃ a : CyclicSubgroups Gal(L/K) → ℤ,
      ∀ (p : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)),
        P.asIdeal.LiesOver p.asIdeal → Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal →
        ∀ n : ℕ,
          (∑ H : CyclicSubgroups Gal(L/K),
            a H * primePowerResidueCount (IntermediateField.fixedField H.val) p n) =
              (Nat.card Gal(L/K) : ℤ) := by
  classical
  obtain ⟨c, hc⟩ := exists_cyclic_conjugate_count_weights Gal(L/K)
  refine ⟨fun H ↦ c H * (Nat.card H.val : ℤ), ?_⟩
  intro p P hP hu n
  let : Finite ((𝓞 L) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let σ : Gal(L/K) := arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal
  have hσ : IsArithFrobAt (𝓞 K) σ P.asIdeal := .arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal
  calc
    _ = ∑ H : CyclicSubgroups Gal(L/K),
        c H * ∑ x : Gal(L/K), if x⁻¹ * σ ^ n * x ∈ H.val then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro H _
      have hterm := frobenius_conjugate_count_eq_prime_degree_sum
        (IntermediateField.fixedField H.val) p P hP hu σ hσ n
      rw [IntermediateField.fixingSubgroup_fixedField] at hterm
      rw [hterm, mul_assoc]
      rfl
    _ = _ := by simpa only [Fintype.card_eq_nat_card] using hc (σ ^ n)

#check @exists_weighted_unramified_prime_power_match
#print axioms exists_weighted_unramified_prime_power_match

end FieldTarget
