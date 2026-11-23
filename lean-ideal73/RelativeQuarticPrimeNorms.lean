import RelativeQuarticIntegerBasis
import GaussianIntegralBasis
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! Recover the norm of each prime factor from the degree of the reduced
polynomial, using the actual quartic order. -/

namespace QuarticModel

open NumberField Polynomial UniqueFactorizationMonoid
open scoped Classical

attribute [local instance] Ideal.Quotient.field

private theorem full_order_coprime (I : Ideal GaussianInt) :
    (conductor GaussianInt thetaHalf).comap (algebraMap GaussianInt (𝓞 K)) ⊔ I = ⊤ := by
  rw [conductor_eq_top_of_adjoin_eq_top gaussian_adjoin_thetaHalf_eq_top, Ideal.comap_top, top_sup_eq]

noncomputable def relativeFactorIdeal (I : Ideal GaussianInt) (Q : GaussianInt[X]) : Ideal (𝓞 K) :=
  I.map (algebraMap GaussianInt (𝓞 K)) ⊔ Ideal.span {aeval thetaHalf Q}

private noncomputable def relativeFactors (I : Ideal GaussianInt) [hI : I.IsMaximal] (hI0 : I ≠ ⊥) :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI0
    (full_order_coprime I) thetaHalf_integral_gaussian

private theorem relativeFactorIdeal_eq {I : Ideal GaussianInt} [hI : I.IsMaximal]
    (hI0 : I ≠ ⊥) (Q : GaussianInt[X])
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      ((minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I))) :
    ((relativeFactors I hI0).symm ⟨_, hQ⟩).val = relativeFactorIdeal I Q := by
  rw [relativeFactors, KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span,
    relativeFactorIdeal, Ideal.span_union, Ideal.span_eq]

theorem relativeFactorIdeal_mem {I : Ideal GaussianInt} [I.IsMaximal] (hI0 : I ≠ ⊥)
    (Q : GaussianInt[X])
    (hQ : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))) :
    relativeFactorIdeal I Q ∈ normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K))) := by
  rw [← thetaHalf_minpoly_gaussian] at hQ
  rw [← relativeFactorIdeal_eq hI0 Q hQ]
  exact ((relativeFactors I hI0).symm ⟨_, hQ⟩).property

theorem exists_relativeFactorIdeal {I : Ideal GaussianInt} [I.IsMaximal]
    (hI0 : I ≠ ⊥) {J : Ideal (𝓞 K)}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))) :
    ∃ Q : GaussianInt[X],
      Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I)) ∧
        J = relativeFactorIdeal I Q := by
  let e := relativeFactors I hI0
  let f := e ⟨J,hJ⟩
  obtain ⟨Q,hQ⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective f.val
  have hmem : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I)) := by
    rw [hQ]
    exact f.property
  have hbase := relativeFactorIdeal_eq hI0 Q hmem
  have hf : (⟨Q.map (Ideal.Quotient.mk I), hmem⟩ : {q // q ∈
      normalizedFactors ((minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I))}) = f :=
    Subtype.ext hQ
  rw [hf] at hbase
  change (e.symm (e ⟨J,hJ⟩)).val = _ at hbase
  rw [e.symm_apply_apply] at hbase
  rw [thetaHalf_minpoly_gaussian] at hmem
  exact ⟨Q,hmem,hbase⟩

/-- The actual residue ring of a prime above `I` is the root extension of
the corresponding irreducible factor of the reduced quadratic. -/
noncomputable def relativeFactorResidueEquiv {I : Ideal GaussianInt} [I.IsMaximal]
    (Q : GaussianInt[X])
    (hQ : Q.map (Ideal.Quotient.mk I) ∣ relativePolynomial.map (Ideal.Quotient.mk I)) :
    (𝓞 K ⧸ relativeFactorIdeal I Q) ≃+*
      ((GaussianInt ⧸ I)[X] ⧸ Ideal.span {Q.map (Ideal.Quotient.mk I)}) := by
  let A := I.map (algebraMap GaussianInt (𝓞 K))
  let H : Ideal (𝓞 K) := Ideal.span {aeval thetaHalf Q}
  let B : Ideal (GaussianInt ⧸ I)[X] :=
    Ideal.span {(minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I)}
  let D : Ideal (GaussianInt ⧸ I)[X] := Ideal.span {Q.map (Ideal.Quotient.mk I)}
  let e : (𝓞 K ⧸ A) ≃+* ((GaussianInt ⧸ I)[X] ⧸ B) :=
    KummerDedekind.quotMapEquivQuotQuotMap (full_order_coprime I) thetaHalf_integral_gaussian
  have he : e (Ideal.Quotient.mk A (aeval thetaHalf Q)) =
      Ideal.Quotient.mk B (Q.map (Ideal.Quotient.mk I)) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact (KummerDedekind.quotMapEquivQuotQuotMap_symm_apply
      (full_order_coprime I) thetaHalf_integral_gaussian Q).symm
  have hmap : D.map (Ideal.Quotient.mk B) =
      (H.map (Ideal.Quotient.mk A)).map (e : (𝓞 K ⧸ A) →+* ((GaussianInt ⧸ I)[X] ⧸ B)) := by
    simp only [D, H, Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, he]
  have hle : B ≤ D := by
    apply Ideal.span_singleton_le_span_singleton.mpr
    simpa only [thetaHalf_minpoly_gaussian] using hQ
  exact (DoubleQuot.quotQuotEquivQuotSup A H).symm.trans <|
    (Ideal.quotientEquiv _ _ e hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)

theorem relativeFactorIdeal_norm {I : Ideal GaussianInt} [I.IsMaximal]
    (Q : GaussianInt[X])
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      (relativePolynomial.map (Ideal.Quotient.mk I))) :
    Ideal.absNorm (relativeFactorIdeal I Q) =
      Nat.card (GaussianInt ⧸ I) ^ (Q.map (Ideal.Quotient.mk I)).natDegree := by
  let F := GaussianInt ⧸ I
  let q : F[X] := Q.map (Ideal.Quotient.mk I)
  have hq : q ≠ 0 := ne_zero_of_mem_normalizedFactors hQ
  let : Module.Finite F (AdjoinRoot q) := (AdjoinRoot.powerBasis hq).finite
  have he := relativeFactorResidueEquiv Q (dvd_of_mem_normalizedFactors hQ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr he.toEquiv).trans ?_
  change Nat.card (AdjoinRoot q) = Nat.card F ^ q.natDegree
  have hd : Module.finrank F (AdjoinRoot q) = q.natDegree := (AdjoinRoot.powerBasis hq).finrank
  rw [Module.natCard_eq_pow_finrank (K := F), hd]

theorem relativeFactorIdeal_inertiaDeg {I : Ideal GaussianInt} [I.IsMaximal]
    [Finite (GaussianInt ⧸ I)] (hI0 : I ≠ ⊥)
    (Q : GaussianInt[X])
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      (relativePolynomial.map (Ideal.Quotient.mk I))) :
    (relativeFactorIdeal I Q).inertiaDeg GaussianInt = (Q.map (Ideal.Quotient.mk I)).natDegree := by
  let : Module.Finite GaussianInt (𝓞 K) := relativeIntegersBasis.finite
  let J := relativeFactorIdeal I Q
  have hJ : J ∈ I.primesOver (𝓞 K) :=
    (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) hI0).mpr (relativeFactorIdeal_mem hI0 Q hQ)
  let : J.LiesOver I := hJ.2
  let : J.IsMaximal := Ideal.isMaximal_of_mem_primesOver hJ
  apply Nat.pow_right_injective (Finite.one_lt_card (α := GaussianInt ⧸ I))
  calc
    Nat.card (GaussianInt ⧸ I) ^ J.inertiaDeg GaussianInt = Ideal.absNorm J := by
      simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using Ideal.cardQuot_pow_inertiaDeg I J
    _ = _ := relativeFactorIdeal_norm Q hQ

/-- The complete multiset of local prime norms, preserving multiplicities. -/
theorem relative_prime_norm_multiset (I : Ideal GaussianInt) [hI : I.IsMaximal] (hI0 : I ≠ ⊥) :
    (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))).map Ideal.absNorm =
      (normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))).map
        (fun q => Nat.card (GaussianInt ⧸ I) ^ q.natDegree) := by
  let N := normalizedFactors ((minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I))
  let e := relativeFactors I hI0
  let base := Nat.card (GaussianInt ⧸ I)
  have hfac := KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
    hI hI0 (full_order_coprime I) thetaHalf_integral_gaussian
  change normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K))) =
    N.attach.map (fun q => (e.symm q).val) at hfac
  have hNorm (q : {q // q ∈ N}) : Ideal.absNorm (e.symm q).val = base ^ q.val.natDegree := by
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective q.val
    have hm : Q.map (Ideal.Quotient.mk I) ∈ N := hQ ▸ q.property
    have he := relativeFactorIdeal_eq hI0 Q hm
    have ht : (⟨Q.map (Ideal.Quotient.mk I), hm⟩ : {q // q ∈ N}) = q := Subtype.ext hQ
    rw [ht] at he
    rw [he, relativeFactorIdeal_norm Q (by simpa only [N, thetaHalf_minpoly_gaussian] using hm), hQ]
  calc
    _ = N.attach.map (fun q => Ideal.absNorm (e.symm q).val) := by
      simpa only [Multiset.map_map, Function.comp_def] using congrArg (Multiset.map Ideal.absNorm) hfac
    _ = N.attach.map (fun q => base ^ q.val.natDegree) :=
      Multiset.map_congr rfl (fun q _ => hNorm q)
    _ = (N.attach.map (fun q => q.val)).map (fun f => base ^ f.natDegree) := by
      rw [Multiset.map_map]
      rfl
    _ = _ := by
      rw [Multiset.attach_map_val]
      simp only [N, base, thetaHalf_minpoly_gaussian]

/-- Transfer a product over distinct primes above a Gaussian prime to a
product on the degrees of distinct irreducible polynomial factors. -/
theorem relative_product_inertiaDeg {M : Type*} [CommMonoid M]
    (I : Ideal GaussianInt) [I.IsMaximal] (hI0 : I ≠ ⊥) (f : ℕ → M) :
    (∏ J ∈ (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))).toFinset,
      f (J.inertiaDeg GaussianInt)) =
      ∏ q ∈ (normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))).toFinset,
        f q.natDegree := by
  let : Finite (GaussianInt ⧸ I) := gaussian_finiteQuotient I hI0
  rw [← thetaHalf_minpoly_gaussian]
  let N := normalizedFactors ((minpoly GaussianInt thetaHalf).map (Ideal.Quotient.mk I))
  let e := relativeFactors I hI0
  have hd (q : {q // q ∈ N}) : (e.symm q).val.inertiaDeg GaussianInt = q.val.natDegree := by
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective q.val
    have hm : Q.map (Ideal.Quotient.mk I) ∈ N := hQ ▸ q.property
    have he := relativeFactorIdeal_eq hI0 Q hm
    have ht : (⟨Q.map (Ideal.Quotient.mk I), hm⟩ : {q // q ∈ N}) = q := Subtype.ext hQ
    rw [ht] at he
    rw [he, relativeFactorIdeal_inertiaDeg hI0 Q
      (by simpa only [N, thetaHalf_minpoly_gaussian] using hm), hQ]
  refine Finset.prod_bij (fun J hJ => (e ⟨J, Multiset.mem_toFinset.mp hJ⟩).val) ?_ ?_ ?_ ?_
  · intro J hJ
    exact Multiset.mem_toFinset.mpr (e ⟨J, Multiset.mem_toFinset.mp hJ⟩).property
  · intro J hJ K' hK he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro q hq
    let q' : {q // q ∈ N} := ⟨q, Multiset.mem_toFinset.mp hq⟩
    refine ⟨(e.symm q').val, Multiset.mem_toFinset.mpr (e.symm q').property, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply q')
  · intro J hJ
    have he := hd (e ⟨J, Multiset.mem_toFinset.mp hJ⟩)
    rw [e.symm_apply_apply] at he
    exact congrArg f he

#print axioms relativeFactorIdeal_mem
#print axioms exists_relativeFactorIdeal
#print axioms relativeFactorResidueEquiv
#print axioms relativeFactorIdeal_norm
#print axioms relativeFactorIdeal_inertiaDeg
#print axioms relative_prime_norm_multiset
#print axioms relative_product_inertiaDeg

end QuarticModel
