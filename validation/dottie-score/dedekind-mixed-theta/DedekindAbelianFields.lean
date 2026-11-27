import DedekindCyclotomicSubfields
import ClassFieldTheory.KroneckerWeber.Core

namespace FieldTarget

open ArtinPrimitiveRootsConjecture NumberField

universe u

/-- The Kronecker–Weber embedding is available for a number field in any universe. -/
theorem cyclotomicEmbedding_of_abelian_numberField
    (K : Type u) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ m : ℕ, 0 < m ∧ Nonempty (K →ₐ[ℚ] CyclotomicField m ℚ) := by
  let : Small.{0} K := small_of_injective (Module.finBasis ℚ K).repr.injective
  let e : Shrink.{0} K ≃+* K := Shrink.ringEquiv K
  let eQ := e.toRatAlgEquiv
  let : NumberField (Shrink.{0} K) :=
    { to_charZero := (RingHom.charZero_iff e.toRingHom.injective).mpr inferInstance
      to_finiteDimensional := Module.Finite.of_surjective eQ.symm.toLinearMap eQ.symm.surjective }
  let : IsAbelianGalois ℚ (Shrink.{0} K) := IsAbelianGalois.of_algHom eQ.toAlgHom
  obtain ⟨m, hm, ⟨ι⟩⟩ := KroneckerWeber.exists_cyclotomicEmbedding (Shrink.{0} K)
  exact ⟨m, hm, ⟨ι.comp eQ.symm.toAlgHom⟩⟩

/-- Dirichlet strip zero locations imply Dedekind RH for every abelian extension of ℚ. -/
theorem dedekindZetaRH_of_dirichlet_of_abelian
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (K : Type u) [Field K] [NumberField K] [IsAbelianGalois ℚ K] : DedekindZetaRH K := by
  obtain ⟨m, hm, ⟨ι⟩⟩ := cyclotomicEmbedding_of_abelian_numberField K
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact dedekindZetaRH_of_cyclotomic_embedding m K ι (hD m)

/-- Taking all abelian number fields is equivalent to taking all Dirichlet characters. -/
theorem abelian_dedekindZetaRH_iff_dirichlet :
    (∀ (K : Type u) [Field K] [NumberField K] [IsAbelianGalois ℚ K], DedekindZetaRH K) ↔
    (∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction) := by
  refine ⟨?_, fun h K ↦ dedekindZetaRH_of_dirichlet_of_abelian h K⟩
  intro h m hm
  let L := CyclotomicField m ℚ
  let e : ULift.{u} L ≃+* L := ULift.ringEquiv
  let eQ := e.toRatAlgEquiv
  let : NumberField (ULift.{u} L) :=
    { to_charZero := (RingHom.charZero_iff e.toRingHom.injective).mpr inferInstance
      to_finiteDimensional := Module.Finite.of_surjective eQ.symm.toLinearMap eQ.symm.surjective }
  let : IsCyclotomicExtension {m} ℚ L := CyclotomicField.isCyclotomicExtension m ℚ
  let : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {m} ℚ L
  let : IsAbelianGalois ℚ (ULift.{u} L) := IsAbelianGalois.of_algHom eQ.toAlgHom
  apply (cyclotomic_dedekindZetaRH_iff_dirichlet m).mp
  intro Z hZ
  exact h (ULift.{u} L) Z ((isDedekindZeta_iff_of_ringEquiv e Z).mpr hZ)

#check @cyclotomicEmbedding_of_abelian_numberField
#check @dedekindZetaRH_of_dirichlet_of_abelian
#check @abelian_dedekindZetaRH_iff_dirichlet
#print axioms KroneckerWeber.exists_cyclotomicEmbedding
#print axioms cyclotomicEmbedding_of_abelian_numberField
#print axioms dedekindZetaRH_of_dirichlet_of_abelian
#print axioms abelian_dedekindZetaRH_iff_dirichlet

end FieldTarget
