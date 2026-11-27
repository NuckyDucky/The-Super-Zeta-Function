import DedekindUnramifiedFrobenius

namespace FieldTarget

open scoped NumberField Pointwise BigOperators Classical
open IsDedekindDomain

private theorem card_smul_fiber {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (a b : X) :
    Nat.card {g : G // g • a = b} = Nat.card (MulAction.stabilizer G a) := by
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G a b
  subst b
  exact Nat.card_congr {
    toFun := fun g ↦ ⟨u⁻¹ * g.val, by
      change (u⁻¹ * g.val) • a = a
      rw [mul_smul, g.property, inv_smul_smul]⟩
    invFun := fun g ↦ ⟨u * g.val, by
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp g.property]⟩
    left_inv := fun g ↦ Subtype.ext (mul_inv_cancel_left u g.val)
    right_inv := fun g ↦ Subtype.ext (inv_mul_cancel_left u g.val) }

private theorem sum_smul_of_pretransitive {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [MulAction.IsPretransitive G X] (a : X) (f : X → ℤ) :
    (∑ g : G, f (g⁻¹ • a)) = (Nat.card (MulAction.stabilizer G a) : ℤ) * ∑ b : X, f b := by
  classical
  calc
    (∑ g : G, f (g⁻¹ • a)) = ∑ g : G, f (g • a) :=
      Fintype.sum_equiv (Equiv.inv G) _ _ fun _ ↦ rfl
    _ = ∑ b : X, ∑ _ : {g : G // g • a = b}, f b :=
      (Fintype.sum_fiberwise' (fun g : G ↦ g • a) f).symm
    _ = _ := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card,
        card_smul_fiber, Finset.mul_sum]

section NumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

local instance (priority := 2000) primesOverGaloisAction (p : Ideal (𝓞 K)) :
    MulAction Gal(L/K) (p.primesOver (𝓞 L)) := Ideal.instMulActionElemPrimesOver

private def contractPrime (E : IntermediateField K L) (p : HeightOneSpectrum (𝓞 K))
    (W : p.asIdeal.primesOver (𝓞 L)) : p.asIdeal.primesOver (𝓞 E) :=
  ⟨W.val.under (𝓞 E), ⟨.under _ _, inferInstance⟩⟩

private def overAsSpectrum {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] (p : HeightOneSpectrum (𝓞 F)) (W : p.asIdeal.primesOver (𝓞 M)) :
    HeightOneSpectrum (𝓞 M) :=
  ⟨W.val, W.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot W.property⟩

private def primeContractionFiberEquiv (E : IntermediateField K L)
    (p : HeightOneSpectrum (𝓞 K)) (Q : p.asIdeal.primesOver (𝓞 E)) :
    {W : p.asIdeal.primesOver (𝓞 L) // contractPrime E p W = Q} ≃
      Q.val.primesOver (𝓞 L) where
  toFun W := ⟨W.val.val, ⟨W.val.property.1, ⟨congrArg Subtype.val W.property.symm⟩⟩⟩
  invFun W := by
    let : W.val.LiesOver Q.val := W.property.2
    let h : W.val.LiesOver p.asIdeal := Ideal.LiesOver.trans _ Q.val _
    exact ⟨⟨W.val, W.property.1, h⟩, Subtype.ext W.property.2.over.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ramification_eq_across_primes
    (p : HeightOneSpectrum (𝓞 K)) (V W : p.asIdeal.primesOver (𝓞 L)) :
    V.val.ramificationIdx (𝓞 K) = W.val.ramificationIdx (𝓞 K) := by
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal V.val Gal(L/K),
      ← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal W.val Gal(L/K)]

private theorem residue_degree_eq_across_primes
    (p : HeightOneSpectrum (𝓞 K)) (V W : p.asIdeal.primesOver (𝓞 L)) :
    V.val.inertiaDeg (𝓞 K) = W.val.inertiaDeg (𝓞 K) := by
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal V.val Gal(L/K),
      ← Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal W.val Gal(L/K)]

private theorem stabilizer_card_mul_contraction_fiber_card
    (E : IntermediateField K L) (p : HeightOneSpectrum (𝓞 K))
    (V : p.asIdeal.primesOver (𝓞 L)) (hV : Algebra.IsUnramifiedAt (𝓞 K) V.val)
    (Q : p.asIdeal.primesOver (𝓞 E)) :
    Nat.card (MulAction.stabilizer Gal(L/K) V) *
        Nat.card {W : p.asIdeal.primesOver (𝓞 L) // contractPrime E p W = Q} =
      Nat.card E.fixingSubgroup * Q.val.inertiaDeg (𝓞 K) := by
  let q := overAsSpectrum p Q
  obtain ⟨W, hWmax, hW⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) q.asIdeal
  let : W.IsMaximal := hWmax
  let : W.LiesOver Q.val := hW
  let hWp : W.LiesOver p.asIdeal := Ideal.LiesOver.trans _ Q.val _
  let U : p.asIdeal.primesOver (𝓞 L) := ⟨W, ⟨hWmax.isPrime, hWp⟩⟩
  let Wtop : HeightOneSpectrum (𝓞 L) := overAsSpectrum p U
  have hvIdx := Ideal.ramificationIdx_eq_one_iff.mpr hV
  have hwIdx : W.ramificationIdx (𝓞 K) = 1 :=
    (ramification_eq_across_primes p V U).symm.trans hvIdx
  have hrelIdx : W.ramificationIdx (𝓞 E) = 1 := by
    have hdiv := Ideal.ramificationIdx_above_dvd (R := 𝓞 K) Q.val W
    rwa [hwIdx, Nat.dvd_one] at hdiv
  have hrelUnram : Algebra.IsUnramifiedAt (𝓞 E) Wtop.asIdeal :=
    Ideal.ramificationIdx_eq_one_iff.mp hrelIdx
  have hvInertia := (unramified_iff_inertia_bot p (overAsSpectrum p V) V.property.2).mp hV
  have hwInertia := (unramified_iff_inertia_bot q Wtop hW).mp hrelUnram
  have hcardV : Nat.card (MulAction.stabilizer Gal(L/K) V) =
      V.val.inertiaDeg (𝓞 K) := by
    have heq : MulAction.stabilizer Gal(L/K) V =
        MulAction.stabilizer Gal(L/K) V.val := by
      ext g
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
        ← Ideal.coe_smul_primesOver]
      constructor
      · exact congrArg Subtype.val
      · intro h
        apply Subtype.ext
        exact h
    rw [heq, Ideal.card_stabilizer_eq_card_inertia_mul_finrank p.asIdeal V.val]
    rw [show Ideal.inertia Gal(L/K) V.val = ⊥ from hvInertia, Subgroup.card_bot, one_mul]
  have hcount := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(L/E)) Q.val W
  rw [show Ideal.inertia Gal(L/E) W = ⊥ from hwInertia, Subgroup.card_bot, mul_one] at hcount
  have hc : (Q.val.primesOver (𝓞 L)).ncard = Nat.card (Q.val.primesOver (𝓞 L)) := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]
  rw [hc] at hcount
  rw [hcardV, Nat.card_congr (primeContractionFiberEquiv E p Q),
    Nat.card_congr E.fixingSubgroupEquiv.toEquiv,
    residue_degree_eq_across_primes p V U]
  change W.inertiaDeg (𝓞 K) * Nat.card (Q.val.primesOver (𝓞 L)) =
    Nat.card Gal(L/E) * Q.val.inertiaDeg (𝓞 K)
  rw [Ideal.inertiaDeg_tower Q.val W, ← hcount]
  ac_rfl

set_option maxHeartbeats 800000 in
/-- The conjugate count for a Frobenius power is the residue-degree count
on the intermediate field multiplied by the fixing subgroup's cardinality. -/
theorem frobenius_conjugate_count_eq_prime_degree_sum
    (E : IntermediateField K L) (p : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 L)) (hP : P.asIdeal.LiesOver p.asIdeal)
    (hUnram : Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal)
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ P.asIdeal) (n : ℕ) :
    (∑ x : Gal(L/K), if x⁻¹ * σ ^ n * x ∈ E.fixingSubgroup then (1 : ℤ) else 0) =
      (Nat.card E.fixingSubgroup : ℤ) * ∑ Q : p.asIdeal.primesOver (𝓞 E),
        if Q.val.inertiaDeg (𝓞 K) ∣ n then (Q.val.inertiaDeg (𝓞 K) : ℤ) else 0 := by
  classical
  let : P.asIdeal.LiesOver p.asIdeal := hP
  let V := Ideal.primesOver.mk p.asIdeal P.asIdeal
  let f : p.asIdeal.primesOver (𝓞 E) → ℤ := fun Q ↦
    if Q.val.inertiaDeg (𝓞 K) ∣ n then 1 else 0
  have hx (x : Gal(L/K)) :
      x⁻¹ * σ ^ n * x ∈ E.fixingSubgroup ↔
        (contractPrime E p (x⁻¹ • V)).val.inertiaDeg (𝓞 K) ∣ n := by
    let U := x⁻¹ • V
    let q := contractPrime E p U
    have hu : Algebra.IsUnramifiedAt (𝓞 K) U.val := by
      rw [← Ideal.ramificationIdx_eq_one_iff, ← ramification_eq_across_primes p V U]
      exact Ideal.ramificationIdx_eq_one_iff.mpr hUnram
    have hU : (overAsSpectrum p U).asIdeal = x⁻¹ • P.asIdeal := by
      change (x⁻¹ • V).val = x⁻¹ • P.asIdeal
      exact Ideal.coe_smul_primesOver x⁻¹ V
    have htw := frobenius_pow_mem_fixingSubgroup_iff E p (overAsSpectrum p q)
      (overAsSpectrum p U) q.property.2 (by exact ⟨rfl⟩) hu
      (x⁻¹ * σ * x) (by rw [hU]; simpa only [inv_inv] using hσ.conj x⁻¹) n
    have hpow : (x⁻¹ * σ * x) ^ n = x⁻¹ * σ ^ n * x := by
      simpa only [MulAut.conj_apply, inv_inv] using (map_pow (MulAut.conj x⁻¹) σ n).symm
    rw [hpow] at htw
    exact htw
  simp_rw [hx]
  change (∑ x : Gal(L/K), (f ∘ contractPrime E p) (x⁻¹ • V)) = _
  rw [sum_smul_of_pretransitive V (f ∘ contractPrime E p)]
  change _ * (∑ W, f (contractPrime E p W)) = _
  rw [← Fintype.sum_fiberwise' (contractPrime E p) f]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [← mul_assoc, ← Nat.cast_mul,
    stabilizer_card_mul_contraction_fiber_card E p V hUnram Q, Nat.cast_mul, mul_assoc]
  by_cases h : Q.val.inertiaDeg (𝓞 K) ∣ n <;> simp [f, h]

#check @frobenius_conjugate_count_eq_prime_degree_sum
#print axioms frobenius_conjugate_count_eq_prime_degree_sum

end NumberFields
end FieldTarget
