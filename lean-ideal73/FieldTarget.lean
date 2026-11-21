/-
The declarations IsDedekindZeta and DedekindZetaRH are copyright 2025
The Formal Conjectures Authors, licensed under the Apache License, Version 2.0.
See FormalConjectures-LICENSE.txt. This file reproduces those two definitions
and adds the continuation and factor transfer proofs below.
-/
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
The next two definitions reproduce Google DeepMind's formal-conjectures declarations
in `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`, commit
`bcb1cdc179c8868c3a7ca651f617c433dcd5102e`, lines 57–64 (Apache-2.0).
The proofs below use Mathlib's identity theorem to compare any two representatives.
-/

namespace ArtinPrimitiveRootsConjecture

def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

def DedekindZetaRH (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

end ArtinPrimitiveRootsConjecture

namespace FieldTarget

open Complex ArtinPrimitiveRootsConjecture

variable {K : Type*} [Field K] [NumberField K]

def StripZerosOnLine (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → F s = 0 → s.re = 1 / 2

theorem continuation_eq_off_one {Z W : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z) (hW : IsDedekindZeta K W) :
    Set.EqOn Z W ({1}ᶜ : Set ℂ) := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have htwo : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hZ.1.analyticOnNhd isOpen_compl_singleton) (hW.1.analyticOnNhd isOpen_compl_singleton)
    hconn htwo
  refine Filter.eventually_of_mem ?_ (fun t (ht : 1 < t.re) ↦ (hZ.2 t ht).trans (hW.2 t ht).symm)
  exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)

/-- Any candidate with the stated regularity and right-half-plane identity supplies
an actual continuation and determines the critical-strip RH proposition. -/
theorem dedekindZetaRH_iff_strip {P : ℂ → ℂ}
    (hP : IsDedekindZeta K P) : DedekindZetaRH K ↔ StripZerosOnLine P := by
  constructor
  · exact fun h ↦ h P hP
  · intro h Z hZ s hs0 hs1 hz
    have hne : s ≠ 1 := by rintro rfl; exact lt_irrefl 1 hs1
    apply h s hs0 hs1
    exact (continuation_eq_off_one hP hZ hne).trans hz

/-- A factorization checked in the half-plane of convergence transfers the field
statement to three strip-zero statements once the product is holomorphic off one. -/
theorem dedekindZetaRH_iff_three_factors {A B C : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ (fun s ↦ A s * B s * C s) {1}ᶜ)
    (hmatch : ∀ s : ℂ, 1 < s.re → A s * B s * C s = NumberField.dedekindZeta K s) :
    DedekindZetaRH K ↔ StripZerosOnLine A ∧ StripZerosOnLine B ∧ StripZerosOnLine C := by
  rw [dedekindZetaRH_iff_strip (P := fun s ↦ A s * B s * C s) ⟨hhol, hmatch⟩]
  constructor
  · intro h
    exact ⟨fun s hl hr hz ↦ h s hl hr (by simp [hz]),
      fun s hl hr hz ↦ h s hl hr (by simp [hz]),
      fun s hl hr hz ↦ h s hl hr (by simp [hz])⟩
  · rintro ⟨hA, hB, hC⟩ s hl hr hz
    change A s * B s * C s = 0 at hz
    rcases mul_eq_zero.mp hz with hab | hc
    · exact (mul_eq_zero.mp hab).elim (hA s hl hr) (hB s hl hr)
    · exact hC s hl hr hc

theorem dedekindZetaRH_iff_third_factor {A B C : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ (fun s ↦ A s * B s * C s) {1}ᶜ)
    (hmatch : ∀ s : ℂ, 1 < s.re → A s * B s * C s = NumberField.dedekindZeta K s)
    (hA : StripZerosOnLine A) (hB : StripZerosOnLine B) :
    DedekindZetaRH K ↔ StripZerosOnLine C := by
  rw [dedekindZetaRH_iff_three_factors hhol hmatch]
  exact ⟨fun h ↦ h.2.2, fun hC ↦ ⟨hA, hB, hC⟩⟩

#print axioms continuation_eq_off_one
#print axioms dedekindZetaRH_iff_third_factor

end FieldTarget
