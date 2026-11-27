import DedekindSolvableQuotient
import Mathlib.FieldTheory.AlgebraicClosure

namespace FieldTarget

open ArtinPrimitiveRootsConjecture NumberField

/-- An embedding into a solvable Galois number field produces an entire
same-input factor for the upper continuation. The embedded field can be in
any universe and need not itself be Galois over the rationals. -/
theorem dedekind_entire_factor_of_solvable_embedding (K : Type*) (L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [IsGalois ℚ L]
    [Group.IsSolvable (L ≃ₐ[ℚ] L)] (ι : K →ₐ[ℚ] L) {ZK ZL : ℂ → ℂ}
    (hK : IsDedekindZeta K ZK) (hL : IsDedekindZeta L ZL) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ w : ℂ, w ≠ 1 → ZL w = g w * ZK w := by
  let F : IntermediateField ℚ L := ι.fieldRange
  let e : K ≃ₐ[ℚ] F := AlgEquiv.ofBijective ι.rangeRestrict
    ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective ι⟩
  let : Group.IsSolvable (L ≃ₐ[F] L) := Group.isSolvable_of_isSolvable_injective
    (f := AlgEquiv.restrictScalarsHom ℚ) (AlgEquiv.restrictScalarsHom_injective ℚ)
  exact dedekind_entire_factor_of_solvable_galois F L
    ((isDedekindZeta_iff_of_ringEquiv e.toRingEquiv ZK).mp hK) hL

theorem dedekindZetaRH_of_solvable_embedding (K : Type*) (L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [IsGalois ℚ L]
    [Group.IsSolvable (L ≃ₐ[ℚ] L)] (ι : K →ₐ[ℚ] L) (hL : DedekindZetaRH L) :
    DedekindZetaRH K := by
  intro ZK hK w hlo hhi hzero
  obtain ⟨ZL, hd, hs⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation L
  have hZL : IsDedekindZeta L ZL := ⟨hd, hs⟩
  obtain ⟨g, _, hprod⟩ := dedekind_entire_factor_of_solvable_embedding K L ι hK hZL
  have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
  exact hL ZL hZL w hlo hhi (by rw [hprod w hw, hzero, mul_zero])

/-- The rational normal closure inside an algebraic closure of the field. -/
abbrev RationalNormalClosure (K : Type) [Field K] [NumberField K] :=
  ↥(IntermediateField.normalClosure ℚ K (AlgebraicClosure K))

instance rationalNormalClosure_numberField (K : Type) [Field K] [NumberField K] :
    NumberField (RationalNormalClosure K) where
  to_charZero := inferInstance
  to_finiteDimensional := normalClosure.is_finiteDimensional ℚ K (AlgebraicClosure K)

instance rationalNormalClosure_isGalois (K : Type) [Field K] [NumberField K] :
    IsGalois ℚ (RationalNormalClosure K) := by
  let : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  exact IsGalois.normalClosure ℚ K (AlgebraicClosure K)

/-- Dedekind RH descends from the canonical normal closure when its Galois
group is solvable. -/
theorem dedekindZetaRH_of_solvable_normalClosure (K : Type) [Field K] [NumberField K]
    [Group.IsSolvable (RationalNormalClosure K ≃ₐ[ℚ] RationalNormalClosure K)]
    (hL : DedekindZetaRH (RationalNormalClosure K)) : DedekindZetaRH K :=
  dedekindZetaRH_of_solvable_embedding K (RationalNormalClosure K)
    (IsScalarTower.toAlgHom ℚ K (RationalNormalClosure K)) hL

#check @dedekind_entire_factor_of_solvable_embedding
#check @dedekindZetaRH_of_solvable_embedding
#check @dedekindZetaRH_of_solvable_normalClosure
#print axioms dedekind_entire_factor_of_solvable_embedding
#print axioms dedekindZetaRH_of_solvable_embedding
#print axioms dedekindZetaRH_of_solvable_normalClosure

end FieldTarget
