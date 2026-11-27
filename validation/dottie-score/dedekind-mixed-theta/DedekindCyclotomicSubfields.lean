import DedekindCyclotomicContinuation
import DedekindZetaZeroFree.LFunctions.Dedekind.EntireAbelianQuotient

namespace FieldTarget

open ArtinPrimitiveRootsConjecture NumberField
open scoped NumberField

/-- The entire zeta quotient for an abelian extension carries every
critical-strip zero of the base field to the extension at the same point. -/
theorem dedekindZetaRH_of_abelian_extension (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hL : DedekindZetaRH L) : DedekindZetaRH K := by
  obtain ⟨fK, fL, g, hKdiff, hLdiff, _, hKseries, hLseries, hquot⟩ :=
    DedekindZetaZeroFree.dedekindAbelianQuotient K L (fun σ τ ↦ mul_comm' σ τ)
  intro Z hZ w hlo hhi hzero
  have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
  have hfK : fK w = 0 :=
    (continuation_eq_off_one ⟨hKdiff, hKseries⟩ hZ hw).trans hzero
  apply hL fL ⟨hLdiff, hLseries⟩ w hlo hhi
  rw [hquot w hw, hfK, mul_zero]

/-- The Dirichlet strip-zero results for a modulus supply Dedekind RH for
each number field equipped with an embedding into that cyclotomic field. -/
theorem dedekindZetaRH_of_cyclotomic_embedding (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] (ι : K →ₐ[ℚ] CyclotomicField m ℚ)
    (hD : ∀ χ : DirichletCharacter ℂ m, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH K := by
  let L := CyclotomicField m ℚ
  let F : IntermediateField ℚ L := ι.fieldRange
  let e : K ≃ₐ[ℚ] F := AlgEquiv.ofBijective ι.rangeRestrict
    ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩
  let _ : IsCyclotomicExtension {m} ℚ L := CyclotomicField.isCyclotomicExtension m ℚ
  let _ : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {m} ℚ L
  have hF := dedekindZetaRH_of_abelian_extension F L
    ((cyclotomic_dedekindZetaRH_iff_dirichlet m).mpr hD)
  intro Z hZ w hlo hhi hzero
  exact hF Z ((isDedekindZeta_iff_of_ringEquiv e.toRingEquiv Z).mp hZ) w hlo hhi hzero

#check @dedekindZetaRH_of_abelian_extension
#check @dedekindZetaRH_of_cyclotomic_embedding
#print axioms dedekindZetaRH_of_abelian_extension
#print axioms dedekindZetaRH_of_cyclotomic_embedding

end FieldTarget
