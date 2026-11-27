import DedekindCyclicZetaProducts
import DedekindSolvableClosure

namespace FieldTarget

open ArtinPrimitiveRootsConjecture
open scoped NumberField BigOperators Classical

/-- For a finite Galois extension, a base-field zero in the right half-plane
away from the pole is an upper-field zero at the same complex input. -/
theorem dedekindZeta_zero_of_galois_extension (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {ZK ZL : ℂ → ℂ} (hK : IsDedekindZeta K ZK) (hL : IsDedekindZeta L ZL)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hz : ZK w = 0) : ZL w = 0 := by
  classical
  let E := fun H : CyclicSubgroups Gal(L/K) ↦ IntermediateField.fixedField H.val
  have hchoose (H : CyclicSubgroups Gal(L/K)) :
      ∃ ZE g : ℂ → ℂ, IsDedekindZeta (E H) ZE ∧
        ∀ z : ℂ, z ≠ 1 → ZL z = g z * ZE z := by
    let e : H.val ≃* (L ≃ₐ[E H] L) := IntermediateField.subgroupEquivAlgEquiv H.val
    let : IsCyclic H.val := H.property
    let : IsCyclic (L ≃ₐ[E H] L) := isCyclic_of_surjective e e.surjective
    obtain ⟨ZE, ZL', g, hEdiff, hLdiff, _, hEseries, hLseries, hprod⟩ :=
      DedekindZetaZeroFree.dedekindAbelianQuotient (E H) L (fun σ τ ↦ mul_comm' σ τ)
    exact ⟨ZE, g, ⟨hEdiff, hEseries⟩, fun z hz1 ↦
      (continuation_eq_off_one hL ⟨hLdiff, hLseries⟩ hz1).trans (hprod z hz1)⟩
  choose ZE g hZE hprod using hchoose
  obtain ⟨S, a, _, hbalance⟩ := exists_cyclic_fixed_field_zeta_product (L := L) hK hZE
  have hcard : Nat.card Gal(L/K) ≠ 0 := Nat.card_pos.ne'
  have hzero := hbalance w hw1
  rw [hz, mul_zero, zero_pow hcard, zero_mul] at hzero
  obtain ⟨H, _, hH⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hEzero : ZE H w = 0 :=
    (mul_eq_zero.mp (eq_zero_of_pow_eq_zero hH)).resolve_left
      (finiteEulerCorrection_ne_zero (E H) S hw)
  rw [hprod H w hw1, hEzero, mul_zero]

theorem dedekindZetaRH_of_galois_extension (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hL : DedekindZetaRH L) : DedekindZetaRH K := by
  intro ZK hK w hlo hhi hz
  obtain ⟨ZL, hd, hs⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation L
  have hZL : IsDedekindZeta L ZL := ⟨hd, hs⟩
  have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
  exact hL ZL hZL w hlo hhi (dedekindZeta_zero_of_galois_extension K L hK hZL hlo hw hz)

/-- The upper field can be a rational Galois field containing an isomorphic
copy of the base field, even if the original field lives in a larger universe. -/
theorem dedekindZetaRH_of_galois_embedding (K : Type*) (L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [IsGalois ℚ L]
    (ι : K →ₐ[ℚ] L) (hL : DedekindZetaRH L) : DedekindZetaRH K := by
  let F : IntermediateField ℚ L := ι.fieldRange
  let e : K ≃ₐ[ℚ] F := AlgEquiv.ofBijective ι.rangeRestrict
    ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective ι⟩
  intro Z hZ
  exact dedekindZetaRH_of_galois_extension F L hL Z
    ((isDedekindZeta_iff_of_ringEquiv e.toRingEquiv Z).mp hZ)

theorem dedekindZetaRH_of_rational_normalClosure (K : Type) [Field K] [NumberField K]
    (hL : DedekindZetaRH (RationalNormalClosure K)) : DedekindZetaRH K :=
  dedekindZetaRH_of_galois_embedding K (RationalNormalClosure K)
    (IsScalarTower.toAlgHom ℚ K (RationalNormalClosure K)) hL

/-- Proving Dedekind RH for finite Galois extensions of the rationals suffices
for every number field, with no restriction on the Galois group. -/
theorem dedekindZetaRH_of_all_galois_over_rat
    (hG : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], DedekindZetaRH F)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  have hsmall (F : Type) [Field F] [NumberField F] :
      ∃ Z, IsDedekindZeta F Z ∧ StripZerosOnLine Z := by
    obtain ⟨Z, hd, hs⟩ := DedekindZetaZeroFree.AbelianQuotient.zetaContinuation F
    have hZ : IsDedekindZeta F Z := ⟨hd, hs⟩
    exact ⟨Z, hZ, dedekindZetaRH_of_rational_normalClosure F (hG (RationalNormalClosure F)) Z hZ⟩
  obtain ⟨Z, hZ, hline⟩ :=
    exists_dedekind_continuation_of_small_fields (K := K) StripZerosOnLine hsmall
  exact (dedekindZetaRH_iff_strip hZ).mpr hline

#check @dedekindZeta_zero_of_galois_extension
#check @dedekindZetaRH_of_galois_embedding
#check @dedekindZetaRH_of_all_galois_over_rat
#print axioms dedekindZeta_zero_of_galois_extension
#print axioms dedekindZetaRH_of_galois_extension
#print axioms dedekindZetaRH_of_galois_embedding
#print axioms dedekindZetaRH_of_rational_normalClosure
#print axioms dedekindZetaRH_of_all_galois_over_rat

end FieldTarget
