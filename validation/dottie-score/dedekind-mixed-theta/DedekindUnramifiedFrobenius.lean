import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius

namespace FieldTarget

open scoped NumberField Pointwise
open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- An unramified prime has trivial inertia for any finite Galois extension. -/
theorem unramified_iff_inertia_bot
    (p : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    (hP : P.asIdeal.LiesOver p.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal ↔ Ideal.inertia Gal(L/K) P.asIdeal = ⊥ := by
  let : P.asIdeal.LiesOver p.asIdeal := hP
  have hcard : Nat.card (Ideal.inertia Gal(L/K) P.asIdeal) =
      P.asIdeal.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) p.asIdeal P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal Gal(L/K)]
  rw [Subgroup.eq_bot_iff_card, hcard]
  exact Ideal.ramificationIdx_eq_one_iff.symm

private theorem frobenius_pow_residue
    (p : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    (hP : P.asIdeal.LiesOver p.asIdeal) (σ : Gal(L/K))
    (hσ : IsArithFrobAt (𝓞 K) σ P.asIdeal) (n : ℕ) (x : 𝓞 L) :
    Ideal.Quotient.mk P.asIdeal ((σ ^ n) • x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ (Nat.card ((𝓞 K) ⧸ p.asIdeal) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hσ.mk_apply ((σ ^ n) • x)
    rw [← hP.over] at h
    change Ideal.Quotient.mk P.asIdeal (σ • ((σ ^ n) • x)) =
      (Ideal.Quotient.mk P.asIdeal ((σ ^ n) • x)) ^ Nat.card ((𝓞 K) ⧸ p.asIdeal) at h
    rw [pow_succ', mul_smul, h, ih, ← pow_mul, ← pow_succ]

/-- The orbit length at an intermediate field is its residue degree.
The extension at the top is Galois and the intermediate field is arbitrary. -/
theorem frobenius_pow_mem_fixingSubgroup_iff
    (E : IntermediateField K L)
    (p : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E))
    (P : HeightOneSpectrum (𝓞 L))
    (hQ : Q.asIdeal.LiesOver p.asIdeal) (hPQ : P.asIdeal.LiesOver Q.asIdeal)
    (hUnram : Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal)
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ P.asIdeal) (n : ℕ) :
    σ ^ n ∈ E.fixingSubgroup ↔ Q.asIdeal.inertiaDeg (𝓞 K) ∣ n := by
  let : Q.asIdeal.LiesOver p.asIdeal := hQ
  let : P.asIdeal.LiesOver Q.asIdeal := hPQ
  have hP : P.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.trans _ Q.asIdeal _
  let : Field ((𝓞 K) ⧸ p.asIdeal) := Ideal.Quotient.field _
  let : Field ((𝓞 E) ⧸ Q.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  let : Finite ((𝓞 E) ⧸ Q.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  let : Finite ((𝓞 L) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ p.asIdeal) := Fintype.ofFinite _
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic ((𝓞 K) ⧸ p.asIdeal) ((𝓞 E) ⧸ Q.asIdeal)
  have hdeg := Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal Q.asIdeal
  have hord : orderOf φ = Q.asIdeal.inertiaDeg (𝓞 K) := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdeg]
  constructor
  · intro hn
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hfixed : (σ ^ n) • algebraMap (𝓞 E) (𝓞 L) x = algebraMap (𝓞 E) (𝓞 L) x := by
      apply Subtype.ext
      exact (E.mem_fixingSubgroup_iff (σ ^ n)).mp hn ((x : E) : L) (x : E).property
    have hpow := frobenius_pow_residue p P hP σ hσ n (algebraMap (𝓞 E) (𝓞 L) x)
    rw [hfixed, Nat.card_eq_fintype_card] at hpow
    have hres : (Ideal.Quotient.mk Q.asIdeal x) ^
        (Fintype.card ((𝓞 K) ⧸ p.asIdeal) ^ n) = Ideal.Quotient.mk Q.asIdeal x := by
      apply (algebraMap ((𝓞 E) ⧸ Q.asIdeal) ((𝓞 L) ⧸ P.asIdeal)).injective
      rw [map_pow, Ideal.Quotient.algebraMap_mk_of_liesOver]
      exact hpow.symm
    change (φ ^ n) (Ideal.Quotient.mk Q.asIdeal x) = _
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    exact hres
  · rintro ⟨m, rfl⟩
    let τ : Gal(L/E) := arithFrobAt (𝓞 E) Gal(L/E) P.asIdeal
    let τK : Gal(L/K) := (E.fixingSubgroupEquiv.symm τ).val
    have hτ : IsArithFrobAt (𝓞 E) τ P.asIdeal := .arithFrobAt (𝓞 E) Gal(L/E) P.asIdeal
    have hqCard : Nat.card ((𝓞 E) ⧸ Q.asIdeal) =
        Nat.card ((𝓞 K) ⧸ p.asIdeal) ^ Q.asIdeal.inertiaDeg (𝓞 K) := by
      rw [hdeg]
      exact Module.natCard_eq_pow_finrank
    have hsame (x : 𝓞 L) :
        Ideal.Quotient.mk P.asIdeal ((σ ^ Q.asIdeal.inertiaDeg (𝓞 K)) • x) =
          Ideal.Quotient.mk P.asIdeal (τK • x) := by
      rw [frobenius_pow_residue p P hP σ hσ, ← hqCard]
      have h := hτ.mk_apply x
      rw [← hPQ.over] at h
      exact h.symm
    have hinertia : σ ^ Q.asIdeal.inertiaDeg (𝓞 K) * τK⁻¹ ∈ Ideal.inertia Gal(L/K) P.asIdeal := by
      intro x
      change (σ ^ Q.asIdeal.inertiaDeg (𝓞 K) * τK⁻¹) • x - x ∈ P.asIdeal
      rw [← Ideal.Quotient.eq, mul_smul]
      simpa only [smul_inv_smul] using hsame (τK⁻¹ • x)
    rw [(unramified_iff_inertia_bot p P hP).mp hUnram, Subgroup.mem_bot] at hinertia
    rw [pow_mul, mul_inv_eq_one.mp hinertia]
    exact E.fixingSubgroup.pow_mem (E.fixingSubgroupEquiv.symm τ).property _

#check @frobenius_pow_mem_fixingSubgroup_iff
#print axioms unramified_iff_inertia_bot
#print axioms frobenius_pow_mem_fixingSubgroup_iff

end FieldTarget
