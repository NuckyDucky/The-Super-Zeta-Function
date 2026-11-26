import GaussianClosureUnramified
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-! Arithmetic Frobenius in the marked normal closure of the archived quartic. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open Finset NumberField UniqueFactorizationMonoid
open scoped Pointwise

noncomputable section

abbrev ClosureAut := L ≃ₐ[ℚ] L

attribute [local instance] Ideal.Quotient.field

local instance : IsGaloisGroup ClosureAut ℤ (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing ClosureAut ℤ (𝓞 L) ℚ L

private theorem rationalQuotient_card (p : ℕ) :
    Nat.card (ℤ ⧸ rationalPrimeIdeal p) = p :=
  (Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv).trans (Nat.card_zmod p)

private theorem closurePrimeFiber_natCast_mem {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) : (p : 𝓞 L) ∈ P := by
  have hf := (mem_closurePrimeFiber_iff hp).mp hP
  simpa only [map_natCast] using
    (Ideal.liesOver_span_iff hf.1.ne_top (Nat.prime_iff_prime_int.mp hp)).mp hf.2

private theorem closurePrimeFiber_ne_bot {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) : P ≠ ⊥ := by
  intro he
  have hm := closurePrimeFiber_natCast_mem hp hP
  rw [he, Ideal.mem_bot, Nat.cast_eq_zero] at hm
  exact hp.ne_zero hm

theorem closurePrimeFiber_isMaximal {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) : P.IsMaximal :=
  ((mem_closurePrimeFiber_iff hp).mp hP).1.isMaximal (closurePrimeFiber_ne_bot hp hP)

private theorem closurePrimeFiber_finite {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) : Finite (𝓞 L ⧸ P) := by
  rw [← Ideal.absNorm_ne_zero_iff, ne_eq, Ideal.absNorm_eq_zero_iff]
  exact closurePrimeFiber_ne_bot hp hP

theorem closurePrimeFiber_charP {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) : CharP (𝓞 L ⧸ P) p := by
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
  exact closurePrimeFiber_natCast_mem hp hP

theorem closurePrimeFiber_nonempty {p : ℕ} (hp : p.Prime) :
    (closurePrimeFiber p).Nonempty := by
  let : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
  have hk : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ rationalPrimeIdeal p := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 L))]
    exact bot_le
  obtain ⟨P, hP, hOver⟩ := (rationalPrimeIdeal p).exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 L) hk
  exact ⟨P, (mem_closurePrimeFiber_iff hp).mpr ⟨hP, ⟨hOver.symm⟩⟩⟩

private theorem integerAction_label_apply (σ : ClosureAut) (a : 𝓞 L) :
    integerAction (closureGaloisEquiv σ) a = σ • a := by
  change RingOfIntegers.mapRingEquiv
    (closureGaloisEquiv.symm (closureGaloisEquiv σ)).toRingEquiv a = _
  rw [closureGaloisEquiv.symm_apply_apply]
  rfl

theorem arithmeticFrobenius_reading {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) {σ : ClosureAut}
    (hσ : IsArithFrobAt ℤ σ P) (a : 𝓞 L) :
    Ideal.Quotient.mk P (integerAction (closureGaloisEquiv σ) a) =
      (Ideal.Quotient.mk P a) ^ p := by
  let : P.LiesOver (rationalPrimeIdeal p) := ((mem_closurePrimeFiber_iff hp).mp hP).2
  have hb := AlgHom.IsArithFrobAt.mk_apply hσ a
  rw [← Ideal.over_def P (rationalPrimeIdeal p), rationalQuotient_card] at hb
  rw [integerAction_label_apply]
  exact hb

theorem closurePrimeFiber_exists_frobenius {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) :
    ∃ σ : ClosureAut, IsArithFrobAt ℤ σ P := by
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  let : Finite (𝓞 L ⧸ P) := closurePrimeFiber_finite hp hP
  exact IsArithFrobAt.exists_of_isInvariant ℤ ClosureAut P

private theorem integerAction_comap (P : Ideal (𝓞 L)) (g : GaussianClosureGroup) :
    P.comap (integerAction g).toRingHom = (closureGaloisEquiv.symm g)⁻¹ • P := by
  rw [Ideal.pointwise_smul_eq_comap, map_inv]
  rfl

theorem closurePrimeFiber_intersection {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr L) {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) :
    Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)) =
      ⨅ g : GaussianClosureGroup, P.comap (integerAction g).toRingHom := by
  classical
  have hf := (mem_closurePrimeFiber_iff hp).mp hP
  let : P.IsPrime := hf.1
  let : P.LiesOver (rationalPrimeIdeal p) := hf.2
  let : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
  have hPair : (closurePrimeFiber p : Set (Ideal (𝓞 L))).Pairwise
      (fun Q Q' => IsCoprime Q Q') := by
    intro Q hQ Q' hQ' hne
    exact Ideal.isCoprime_iff_sup_eq.mpr ((closurePrimeFiber_isMaximal hp hQ).coprime_of_ne
      (closurePrimeFiber_isMaximal hp hQ') hne)
  have hProd : (∏ Q ∈ closurePrimeFiber p, Q) = Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)) :=
    closurePrimeFiber_product hp (fun _ hQ => closurePrimeFiber_unramified hp hd hQ)
  rw [← hProd, Ideal.prod_eq_iInf_of_pairwise_isCoprime hPair]
  apply le_antisymm
  · refine le_iInf fun g => ?_
    rw [integerAction_comap]
    let τ := (closureGaloisEquiv.symm g)⁻¹
    have hQ : τ • P ∈ (rationalPrimeIdeal p).primesOver (𝓞 L) :=
      ⟨inferInstance, ⟨(Ideal.over_def P (rationalPrimeIdeal p)).trans
        (Ideal.under_smul (A := ℤ) (g := τ) (P := P)).symm⟩⟩
    exact iInf_le_of_le (τ • P) (iInf_le _ ((mem_closurePrimeFiber_iff hp).mpr hQ))
  · refine le_iInf fun Q => le_iInf fun hQ => ?_
    have hQ' := (mem_closurePrimeFiber_iff hp).mp hQ
    let : Q.IsPrime := hQ'.1
    let : Q.LiesOver (rationalPrimeIdeal p) := hQ'.2
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (rationalPrimeIdeal p) P Q ClosureAut
    refine iInf_le_of_le (closureGaloisEquiv τ⁻¹) ?_
    rw [integerAction_comap, closureGaloisEquiv.symm_apply_apply, inv_inv, hτ]

/-- The residue cardinal and the stabilizer at an unramified prime,
expressed in the same marked labels as the minor-ideal count. -/
theorem arithmeticFrobenius_local_data {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr L) {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p)
    {σ : ClosureAut} (hσ : IsArithFrobAt ℤ σ P) :
    Nat.card (𝓞 L ⧸ P) = p ^ orderOf (closureGaloisEquiv σ) ∧
    ∀ g : GaussianClosureGroup, P.comap (integerAction g).toRingHom = P ↔
      ∃ j : Fin 4, closureGaloisEquiv σ ^ (j : ℕ) = g := by
  classical
  let q := rationalPrimeIdeal p
  let : q.IsMaximal := rationalPrimeIdeal_isMaximal hp
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  let : P.LiesOver q := ((mem_closurePrimeFiber_iff hp).mp hP).2
  let : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) (Nat.prime_iff_prime_int.mp hp)).mp
      hd P inferInstance ((mem_closurePrimeFiber_iff hp).mp hP).2
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (ℤ ⧸ q) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  let : Fintype (ℤ ⧸ q) := Fintype.ofFinite _
  let : Finite (𝓞 L ⧸ P) := closurePrimeFiber_finite hp hP
  let : Fintype (𝓞 L ⧸ P) := Fintype.ofFinite _
  let M := Ideal.Quotient.stabilizerHom P q ClosureAut
  let f : MulAction.stabilizer ClosureAut P := ⟨σ, IsArithFrobAt.mem_stabilizer hσ⟩
  let F := FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ q) (𝓞 L ⧸ P)
  have hq : Fintype.card (ℤ ⧸ q) = p := by
    rw [← Nat.card_eq_fintype_card, rationalQuotient_card]
  have hMf : M f = F := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hq]
    change Ideal.Quotient.mk P (σ • a) = (Ideal.Quotient.mk P a) ^ p
    rw [← integerAction_label_apply]
    exact arithmeticFrobenius_reading hp hP hσ a
  have hInertia : Nat.card (P.inertia ClosureAut) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := ClosureAut) q P,
      Ideal.ramificationIdxIn_eq_ramificationIdx q P ClosureAut, Ideal.ramificationIdx_eq_one]
  have hM : Function.Injective M := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (Subgroup.map_eq_bot_iff_of_injective (f := (MulAction.stabilizer ClosureAut P).subtype)
      M.ker Subtype.coe_injective).mp
    change (Ideal.Quotient.stabilizerHom P q ClosureAut).ker.map
      (MulAction.stabilizer ClosureAut P).subtype = ⊥
    rw [Ideal.Quotient.map_ker_stabilizer_subtype]
    exact Subgroup.eq_bot_of_card_eq _ hInertia
  have hOrder : orderOf (closureGaloisEquiv σ) = Module.finrank (ℤ ⧸ q) (𝓞 L ⧸ P) := by
    rw [MulEquiv.orderOf_eq]
    change orderOf ((MulAction.stabilizer ClosureAut P).subtype f) = _
    rw [orderOf_injective (MulAction.stabilizer ClosureAut P).subtype Subtype.coe_injective f,
      ← orderOf_injective M hM f, hMf,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  refine ⟨?_, fun g => ?_⟩
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ℤ ⧸ q), hq, hOrder]
  · constructor
    · intro hfix
      rw [integerAction_comap, ← MulAction.mem_stabilizer_iff, Subgroup.inv_mem_iff] at hfix
      let t : MulAction.stabilizer ClosureAut P := ⟨closureGaloisEquiv.symm g, hfix⟩
      obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ℤ ⧸ q) (𝓞 L ⧸ P)).2 (M t)
      have hj' : f ^ (j : ℕ) = t := hM (by rw [map_pow, hMf]; exact hj)
      have hj'' : (closureGaloisEquiv σ) ^ (j : ℕ) = g := by
        have hv := congrArg (fun v : MulAction.stabilizer ClosureAut P => v.val) hj'
        change ((f ^ (j : ℕ) : MulAction.stabilizer ClosureAut P) : ClosureAut) = t.val at hv
        rw [Subgroup.coe_pow] at hv
        change σ ^ (j : ℕ) = closureGaloisEquiv.symm g at hv
        rw [← map_pow, hv, closureGaloisEquiv.apply_symm_apply]
      let a := closureGaloisEquiv σ
      have h4 : orderOf a ≤ 4 :=
        orderOf_le_of_pow_eq_one (by decide) (gaussianD4_pow_four a)
      exact ⟨⟨(j : ℕ) % orderOf a, (Nat.mod_lt _ (orderOf_pos a)).trans_le h4⟩,
        (pow_mod_orderOf a _).trans hj''⟩
    · rintro ⟨j, rfl⟩
      rw [integerAction_comap, ← MulAction.mem_stabilizer_iff, Subgroup.inv_mem_iff,
        map_pow, closureGaloisEquiv.symm_apply_apply]
      exact (MulAction.stabilizer ClosureAut P).pow_mem f.property _

/-- A representative at any chosen prime above `p` gives the same
matching exponents at every prime above `p`. Both labels are central. -/
theorem retainedMinor_exponents_of_arithmeticFrobenius {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr L) {P₀ : Ideal (𝓞 L)} (hP₀ : P₀ ∈ closurePrimeFiber p)
    {σ : ClosureAut} (hσ : IsArithFrobAt ℤ σ P₀)
    {x : ℝ} (hx : 2 ≤ x) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) (label : GaussianClosureGroup)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    (normalizedFactors (sqrtFrobeniusMinorIdeal x (integerAction label).toRingHom)).count P =
      if closureGaloisEquiv σ = label then
        frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p else 0 := by
  classical
  have hf := (mem_closurePrimeFiber_iff hp).mp hP
  have hf₀ := (mem_closurePrimeFiber_iff hp).mp hP₀
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  let : P₀.IsPrime := hf₀.1
  let : P.LiesOver (rationalPrimeIdeal p) := hf.2
  let : P₀.LiesOver (rationalPrimeIdeal p) := hf₀.2
  let : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (rationalPrimeIdeal p) P₀ P ClosureAut
  let ρ := τ * σ * τ⁻¹
  have hρ : IsArithFrobAt ℤ ρ P := hτ ▸ hσ.conj τ
  have hData := arithmeticFrobenius_local_data hp hd hP hρ
  let : Finite (𝓞 L ⧸ P) := closurePrimeFiber_finite hp hP
  let : Fintype (𝓞 L ⧸ P) := Fintype.ofFinite _
  let : CharP (𝓞 L ⧸ P) p := closurePrimeFiber_charP hp hP
  have hCard : Fintype.card (𝓞 L ⧸ P) = p ^ orderOf (closureGaloisEquiv ρ) :=
    Nat.card_eq_fintype_card.symm.trans hData.1
  have hc : Commute (closureGaloisEquiv τ) label := by
    rcases hLabel with rfl | rfl
    · exact Commute.one_right _
    · exact gaussianCentral_commute_all _
  have hc' : closureGaloisEquiv τ * label * (closureGaloisEquiv τ)⁻¹ = label := by
    rw [hc.eq, mul_inv_cancel_right]
  have hLabelEq : closureGaloisEquiv ρ = label ↔ closureGaloisEquiv σ = label := by
    dsimp [ρ]
    simp only [map_mul, map_inv]
    exact ⟨fun h => mul_left_cancel (mul_right_cancel (h.trans hc'.symm)),
      fun h => h ▸ hc'⟩
  simpa only [hLabelEq] using sqrtFrobeniusD4MinorIdeal_count P integerAction hx hp hLow
    (closureGaloisEquiv ρ) label (closurePrimeFiber_unramified hp hd hP)
    (closurePrimeFiber_intersection hp hd hP) hCard hData.2
    (arithmeticFrobenius_reading hp hP hρ) hLabel

#print axioms closurePrimeFiber_nonempty
#print axioms closurePrimeFiber_charP
#print axioms arithmeticFrobenius_reading
#print axioms closurePrimeFiber_intersection
#print axioms arithmeticFrobenius_local_data
#print axioms closurePrimeFiber_exists_frobenius
#print axioms retainedMinor_exponents_of_arithmeticFrobenius

end
end GaussianQuarticClosure
end AlpogeSuperZeta
