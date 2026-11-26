import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The finite group calculation for prime weights read through a fixed
CM field. The use of the Galois intersection and Chebotarev is given in
the accompanying note. -/

namespace AlpogeSuperZeta

abbrev GaussianClosureGroup := DihedralGroup 4

/-- The element that negates both square roots in the normal closure. -/
def gaussianCentralElement : GaussianClosureGroup := .r 2

theorem gaussianCentralElement_eq_commutator :
    gaussianCentralElement =
      (.r 1 : GaussianClosureGroup) * .sr 0 * (.r 1)⁻¹ * (.sr 0)⁻¹ := by
  decide +kernel

/-- A quotient in which complex conjugation commutes with the rotation
identifies the central Frobenius class with the identity. -/
theorem gaussianCentralElement_eq_one_in_cm_quotient {H : Type*} [Group H]
    (f : GaussianClosureGroup →* H) (h : Commute (f (.r 1)) (f (.sr 0))) :
    f gaussianCentralElement = 1 := by
  rw [gaussianCentralElement_eq_commutator, map_mul, map_mul, map_mul, map_inv,
    map_inv, h.eq]
  group

/-- Inert degree-one count above a rational prime in the Gaussian base. -/
def gaussianInertFrobeniusWeight (g : GaussianClosureGroup) : ℕ :=
  if g = gaussianCentralElement then 2
  else if g = .sr 1 ∨ g = .sr 3 then 1 else 0

/-- Inert degree-one count above a rational prime in the biquadratic base. -/
def biquadraticInertFrobeniusWeight (g : GaussianClosureGroup) : ℕ :=
  if g = gaussianCentralElement then 4 else 0

/-- The least weight constant on each central pair and dominating the
original weight at both members of that pair. -/
def centralPairMajorant (a : GaussianClosureGroup → ℕ) (g : GaussianClosureGroup) : ℕ :=
  max (a g) (a (gaussianCentralElement * g))

theorem centralPairMajorant_invariant (a : GaussianClosureGroup → ℕ)
    (g : GaussianClosureGroup) :
    centralPairMajorant a (gaussianCentralElement * g) = centralPairMajorant a g := by
  have hsq : gaussianCentralElement * gaussianCentralElement = 1 := by decide +kernel
  simp [centralPairMajorant, ← mul_assoc, hsq, max_comm]

theorem centralPairMajorant_le (a f : GaussianClosureGroup → ℕ)
    (hf : ∀ g, f (gaussianCentralElement * g) = f g) (ha : ∀ g, a g ≤ f g) :
    ∀ g, centralPairMajorant a g ≤ f g :=
  fun g => max_le (ha g) (hf g ▸ ha (gaussianCentralElement * g))

theorem gaussian_inert_central_pair_totals :
    (∑ g : GaussianClosureGroup, gaussianInertFrobeniusWeight g) = 4 ∧
    (∑ g : GaussianClosureGroup, centralPairMajorant gaussianInertFrobeniusWeight g) = 6 ∧
    (∑ g : GaussianClosureGroup, biquadraticInertFrobeniusWeight g) = 4 ∧
    (∑ g : GaussianClosureGroup, centralPairMajorant biquadraticInertFrobeniusWeight g) = 8 := by
  decide +kernel

#print axioms gaussianCentralElement_eq_commutator
#print axioms gaussianCentralElement_eq_one_in_cm_quotient
#print axioms centralPairMajorant_invariant
#print axioms centralPairMajorant_le
#print axioms gaussian_inert_central_pair_totals

end AlpogeSuperZeta
