import DedekindAbelianFields
import Mathlib.GroupTheory.Solvable

namespace FieldTarget

open ArtinPrimitiveRootsConjecture NumberField

private theorem commutator_fixedField_isAbelian (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsAbelianGalois K (IntermediateField.fixedField (commutator (L ≃ₐ[K] L))) := by
  let q : Abelianization (L ≃ₐ[K] L) ≃*
      (IntermediateField.fixedField (commutator (L ≃ₐ[K] L)) ≃ₐ[K]
        IntermediateField.fixedField (commutator (L ≃ₐ[K] L))) :=
    IsGalois.normalAutEquivQuotient (commutator (L ≃ₐ[K] L))
  refine { is_comm.comm := ?_ }
  intro σ τ
  apply q.symm.injective
  rw [map_mul, map_mul]
  exact @mul_comm (Abelianization (L ≃ₐ[K] L)) inferInstance (q.symm σ) (q.symm τ)

private theorem abelian_entire_factor (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    {ZK ZL : ℂ → ℂ} (hK : IsDedekindZeta K ZK) (hL : IsDedekindZeta L ZL) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ w : ℂ, w ≠ 1 → ZL w = g w * ZK w := by
  obtain ⟨fK, fL, g, hKdiff, hLdiff, hg, hKseries, hLseries, hquot⟩ :=
    DedekindZetaZeroFree.dedekindAbelianQuotient K L hcomm
  refine ⟨g, hg, fun w hw ↦ ?_⟩
  exact (continuation_eq_off_one hL ⟨hLdiff, hLseries⟩ hw).trans <|
    (hquot w hw).trans (congrArg (g w * ·) (continuation_eq_off_one ⟨hKdiff, hKseries⟩ hK hw))

private theorem solvable_entire_factor_induction (L : Type) [Field L] [NumberField L]
    (n : ℕ) : ∀ (K : Type) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
      [Group.IsSolvable (L ≃ₐ[K] L)], Module.finrank K L = n →
      ∀ {ZK ZL : ℂ → ℂ}, IsDedekindZeta K ZK → IsDedekindZeta L ZL →
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ w : ℂ, w ≠ 1 → ZL w = g w * ZK w := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ _ _ _ hn ZK ZL hK hL
    let G := L ≃ₐ[K] L
    by_cases htrivial : Subsingleton G
    · exact abelian_entire_factor K L (fun σ τ ↦ htrivial.elim (σ * τ) (τ * σ)) hK hL
    let : Nontrivial G := not_subsingleton_iff_nontrivial.mp htrivial
    let F : IntermediateField K L := IntermediateField.fixedField (commutator G)
    have hFdegree : Module.finrank F L < n := by
      rw [← hn, IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K L]
      simpa only [Subgroup.card_top] using
        Subgroup.card_lt_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G)
    let e := IntermediateField.subgroupEquivAlgEquiv (commutator G)
    let : Group.IsSolvable (L ≃ₐ[F] L) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    obtain ⟨ZF, hFdiff, hFseries⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation F
    have hF : IsDedekindZeta F ZF := ⟨hFdiff, hFseries⟩
    obtain ⟨b, hb, hb_eq⟩ := ih (Module.finrank F L) hFdegree F rfl hF hL
    let : IsAbelianGalois K F := commutator_fixedField_isAbelian K L
    obtain ⟨a, ha, ha_eq⟩ := abelian_entire_factor K F (fun σ τ ↦ mul_comm' σ τ) hK hF
    refine ⟨fun w ↦ b w * a w, hb.mul ha, fun w hw ↦ ?_⟩
    rw [hb_eq w hw, ha_eq w hw, mul_assoc]

/-- In a solvable Galois extension, the upper Dedekind continuation is the lower
one multiplied by an entire function, with the identity valid away from one. -/
theorem dedekind_entire_factor_of_solvable_galois (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)]
    {ZK ZL : ℂ → ℂ} (hK : IsDedekindZeta K ZK) (hL : IsDedekindZeta L ZL) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ w : ℂ, w ≠ 1 → ZL w = g w * ZK w :=
  solvable_entire_factor_induction L (Module.finrank K L) K rfl hK hL

/-- An upper-field critical-line result descends along a solvable Galois extension. -/
theorem dedekindZetaRH_of_solvable_galois_extension (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] (hL : DedekindZetaRH L) : DedekindZetaRH K := by
  intro ZK hK w hlo hhi hzero
  obtain ⟨ZL, hLdiff, hLseries⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation L
  have hZL : IsDedekindZeta L ZL := ⟨hLdiff, hLseries⟩
  obtain ⟨g, _, hg⟩ := dedekind_entire_factor_of_solvable_galois K L hK hZL
  have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
  exact hL ZL hZL w hlo hhi (by rw [hg w hw, hzero, mul_zero])

/-- After the lower field satisfies Dedekind RH, the upper field's remaining
zero-location statement is exactly the statement for its entire factor. -/
theorem dedekindZetaRH_iff_entire_factor_of_solvable_galois (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] {ZK ZL : ℂ → ℂ}
    (hK : IsDedekindZeta K ZK) (hL : IsDedekindZeta L ZL) (hline : DedekindZetaRH K) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ w : ℂ, w ≠ 1 → ZL w = g w * ZK w) ∧
      (DedekindZetaRH L ↔ StripZerosOnLine g) := by
  obtain ⟨g, hd, hg⟩ := dedekind_entire_factor_of_solvable_galois K L hK hL
  refine ⟨g, hd, hg, ?_⟩
  rw [dedekindZetaRH_iff_strip hL]
  constructor
  · intro h w hlo hhi hz
    have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
    exact h w hlo hhi (by rw [hg w hw, hz, zero_mul])
  · intro h w hlo hhi hz
    have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
    rw [hg w hw, mul_eq_zero] at hz
    exact hz.elim (h w hlo hhi) (hline ZK hK w hlo hhi)

/-- For a solvable Galois number field, the rational Dirichlet premise handles
the commutator-fixed subfield and leaves the entire relative factor. -/
theorem dedekindZetaRH_iff_factor_over_abelian_subfield
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [Group.IsSolvable (L ≃ₐ[ℚ] L)]
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction) :
    let F := IntermediateField.fixedField (commutator (L ≃ₐ[ℚ] L))
    ∃ ZF ZL g : ℂ → ℂ, IsDedekindZeta F ZF ∧ IsDedekindZeta L ZL ∧ Differentiable ℂ g ∧
      (∀ w : ℂ, w ≠ 1 → ZL w = g w * ZF w) ∧ (DedekindZetaRH L ↔ StripZerosOnLine g) := by
  dsimp only
  let F := IntermediateField.fixedField (commutator (L ≃ₐ[ℚ] L))
  let : IsAbelianGalois ℚ F := commutator_fixedField_isAbelian ℚ L
  let e := IntermediateField.subgroupEquivAlgEquiv (commutator (L ≃ₐ[ℚ] L))
  let : Group.IsSolvable (L ≃ₐ[F] L) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  obtain ⟨ZF, hFdiff, hFseries⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation F
  obtain ⟨ZL, hLdiff, hLseries⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation L
  have hF : IsDedekindZeta F ZF := ⟨hFdiff, hFseries⟩
  have hL : IsDedekindZeta L ZL := ⟨hLdiff, hLseries⟩
  obtain ⟨g, hd, hprod, hiff⟩ := dedekindZetaRH_iff_entire_factor_of_solvable_galois F L hF hL
    (dedekindZetaRH_of_dirichlet_of_abelian hD F)
  exact ⟨ZF, ZL, g, hF, hL, hd, hprod, hiff⟩

#check @dedekind_entire_factor_of_solvable_galois
#check @dedekindZetaRH_of_solvable_galois_extension
#check @dedekindZetaRH_iff_entire_factor_of_solvable_galois
#check @dedekindZetaRH_iff_factor_over_abelian_subfield
#print axioms dedekind_entire_factor_of_solvable_galois
#print axioms dedekindZetaRH_of_solvable_galois_extension
#print axioms dedekindZetaRH_iff_entire_factor_of_solvable_galois
#print axioms dedekindZetaRH_iff_factor_over_abelian_subfield

end FieldTarget
