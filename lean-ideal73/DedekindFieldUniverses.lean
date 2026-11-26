import FieldTarget
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace FieldTarget

open ArtinPrimitiveRootsConjecture NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

private theorem norm_map_ringOfIntegers (e : K ≃+* L) (I : Ideal (𝓞 K)) :
    (I.map (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 L)).absNorm = I.absNorm := by
  classical
  let f := RingOfIntegers.mapRingEquiv e
  let J := I.map (f : 𝓞 K →+* 𝓞 L)
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I J f rfl).toEquiv).symm

/-- An isomorphism of fields gives a bijection of the ideals of each norm. -/
theorem dedekindZeta_eq_of_ringEquiv (e : K ≃+* L) (w : ℂ) :
    NumberField.dedekindZeta K w = NumberField.dedekindZeta L w := by
  have h (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} =
      Nat.card {J : Ideal (𝓞 L) // J.absNorm = n} := by
    let f := (RingOfIntegers.mapRingEquiv e).idealComapOrderIso.symm.toEquiv
    refine Nat.card_congr (f.subtypeEquiv fun I => ?_)
    change I.absNorm = n ↔ (I.map (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 L)).absNorm = n
    rw [norm_map_ringOfIntegers e]
  simp only [NumberField.dedekindZeta, h]

/-- The same complex function is a continuation for isomorphic number fields. -/
theorem isDedekindZeta_iff_of_ringEquiv (e : K ≃+* L) (Z : ℂ → ℂ) :
    IsDedekindZeta K Z ↔ IsDedekindZeta L Z := by
  simp only [IsDedekindZeta, dedekindZeta_eq_of_ringEquiv e]

/-- A statement about the continuing function can use a proof for number fields
in universe zero, even when the field in the target has a larger universe. -/
theorem exists_dedekind_continuation_of_small_fields
    (P : (ℂ → ℂ) → Prop)
    (h : ∀ (F : Type) [Field F] [NumberField F], ∃ Z, IsDedekindZeta F Z ∧ P Z) :
    ∃ Z, IsDedekindZeta K Z ∧ P Z := by
  let : Small.{0} K := small_of_injective (Module.finBasis ℚ K).repr.injective
  let e : Shrink.{0} K ≃ₐ[ℚ] K := Shrink.algEquiv ℚ K
  let : CharZero (Shrink.{0} K) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (Shrink.{0} K)).injective
  let : FiniteDimensional ℚ (Shrink.{0} K) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let : NumberField (Shrink.{0} K) := ⟨⟩
  obtain ⟨Z, hZ, hP⟩ := h (Shrink.{0} K)
  exact ⟨Z, (isDedekindZeta_iff_of_ringEquiv e.toRingEquiv Z).mp hZ, hP⟩

#print axioms dedekindZeta_eq_of_ringEquiv
#print axioms isDedekindZeta_iff_of_ringEquiv
#print axioms exists_dedekind_continuation_of_small_fields

end FieldTarget
