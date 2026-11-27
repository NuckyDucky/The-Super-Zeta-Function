import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Linarith

namespace FieldTarget

open Finset
open scoped BigOperators Classical

private theorem exists_upper_weights (α : Type*) [Fintype α] [PartialOrder α] :
    ∃ c : α → ℤ, ∀ a : α, (∑ b : α, if a ≤ b then c b else 0) = 1 := by
  classical
  let : LocallyFiniteOrder (WithTop α) := Fintype.toLocallyFiniteOrder
  let incl : α ↪ WithTop α := ⟨fun a ↦ a, WithTop.coe_injective⟩
  refine ⟨fun b ↦ -IncidenceAlgebra.mu ℤ (incl b) ⊤, ?_⟩
  intro a
  let greater := Finset.univ.filter (a ≤ ·)
  have hI : Finset.Icc (incl a) (⊤ : WithTop α) = insert ⊤ (greater.map incl) := by
    ext x
    cases x using WithTop.recTopCoe <;> simp [greater, incl]
  have ht : (⊤ : WithTop α) ∉ greater.map incl := by simp [greater, incl]
  have hneq : incl a ≠ (⊤ : WithTop α) := WithTop.coe_ne_top
  have hsum := IncidenceAlgebra.sum_Icc_mu_left (𝕜 := ℤ) (incl a) (⊤ : WithTop α)
  rw [ite_eq_right hneq, hI, Finset.sum_insert ht, Finset.sum_map] at hsum
  have htop : IncidenceAlgebra.mu ℤ (⊤ : WithTop α) ⊤ = 1 := by
    simp
  rw [htop] at hsum
  rw [← Finset.sum_filter, Finset.sum_neg_distrib]
  linarith only [hsum]

abbrev CyclicSubgroups (G : Type*) [Group G] := {H : Subgroup G // IsCyclic H}

noncomputable instance cyclicSubgroupsFintype (G : Type*) [Group G] [Finite G] :
    Fintype (CyclicSubgroups G) := by
  let : Finite (CyclicSubgroups G) := Finite.of_injective
    (fun H : CyclicSubgroups G ↦ (H.val : Set G))
    (fun _ _ h ↦ Subtype.ext (SetLike.coe_injective h))
  exact Fintype.ofFinite _

/-- Integer multiplicities on cyclic subgroups can cover every group element
with total multiplicity one. -/
theorem exists_cyclic_subgroup_weights (G : Type*) [Group G]
    [Fintype (CyclicSubgroups G)] :
    ∃ c : CyclicSubgroups G → ℤ, ∀ g : G, (∑ H : CyclicSubgroups G, if g ∈ H.val then c H else 0) = 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_upper_weights (CyclicSubgroups G)
  refine ⟨c, fun g ↦ ?_⟩
  let C : CyclicSubgroups G := ⟨Subgroup.zpowers g, inferInstance⟩
  have hle (H : CyclicSubgroups G) : C ≤ H ↔ g ∈ H.val := by
    change Subgroup.zpowers g ≤ H.val ↔ _
    exact Subgroup.zpowers_le
  simpa only [hle] using hc C

/-- The same weights give the constant character after summing all conjugates.
The inner sum is the numerator of the fixed-coset character. -/
theorem exists_cyclic_conjugate_count_weights (G : Type*) [Group G] [Fintype G] :
    ∃ c : CyclicSubgroups G → ℤ, ∀ g : G,
      (∑ H : CyclicSubgroups G,
        c H * ∑ x : G, if x⁻¹ * g * x ∈ H.val then (1 : ℤ) else 0) = Fintype.card G := by
  classical
  obtain ⟨c, hc⟩ := exists_cyclic_subgroup_weights G
  refine ⟨c, fun g ↦ ?_⟩
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

#check @exists_cyclic_conjugate_count_weights
#print axioms exists_cyclic_subgroup_weights
#print axioms exists_cyclic_conjugate_count_weights

end FieldTarget
