import DedekindCyclicEulerFactors
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.NumberField.Ideal.Basic

namespace FieldTarget

open scoped NumberField BigOperators Classical
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
variable (M : Type*) [Field M] [NumberField M] [Algebra K M]

/-- The usual Dedekind Euler denominator contracted to one base prime. -/
noncomputable def localDedekindDenominator
    (p : HeightOneSpectrum (𝓞 K)) (w : ℂ) : ℂ :=
  ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 M), (1 - (Ideal.absNorm Q : ℂ) ^ (-w))

theorem localDedekindDenominator_self (p : HeightOneSpectrum (𝓞 K)) (w : ℂ) :
    localDedekindDenominator K p w = 1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-w) := by
  classical
  have h : IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K) = {p.asIdeal} := by
    ext Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K), Finset.mem_singleton]
    constructor
    · rintro ⟨_, hover⟩
      simpa [Ideal.under] using hover.over.symm
    · rintro rfl
      exact ⟨p.isPrime, ⟨by simp [Ideal.under]⟩⟩
  unfold localDedekindDenominator
  exact (congrArg (fun S ↦ ∏ Q ∈ S, (1 - (Ideal.absNorm Q : ℂ) ^ (-w))) h).trans
    (Finset.prod_singleton _ _)

private theorem absNorm_gt_one {I : Ideal (𝓞 K)} [I.IsPrime] (hI : I ≠ ⊥) :
    1 < I.absNorm := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have h1 := Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top (inferInstance : I.IsPrime))
  omega

private theorem norm_neg_cpow_lt_one {n : ℕ} (hn : 1 < n) {w : ℂ} (hw : 0 < w.re) :
    ‖(n : ℂ) ^ (-w)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (neg_lt_zero.mpr hw)

private theorem sub_one_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hz
  exact (lt_irrefl 1) hz

theorem localDedekindDenominator_ne_zero
    (p : HeightOneSpectrum (𝓞 K)) {w : ℂ} (hw : 0 < w.re) :
    localDedekindDenominator M p w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro Q hQ
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 M)).mp hQ
  let : Q.IsPrime := hmem.1
  exact sub_one_ne_zero_of_norm_lt_one
    (norm_neg_cpow_lt_one (absNorm_gt_one (Ideal.ne_bot_of_mem_primesOver p.ne_bot hmem)) hw)

theorem differentiable_localDedekindDenominator (p : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ (localDedekindDenominator M p) := by
  apply Differentiable.fun_finsetProd
  intro Q hQ
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 M)).mp hQ
  have hnorm := Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.ne_bot_of_mem_primesOver p.ne_bot hmem)
  exact Differentiable.sub (differentiable_const (1 : ℂ))
    ((Differentiable.neg differentiable_id).const_cpow (Or.inl (by exact_mod_cast hnorm)))

private theorem basePrime_pow_inertiaDeg
    (p : HeightOneSpectrum (𝓞 K)) (Q : p.asIdeal.primesOver (𝓞 M)) (w : ℂ) :
    ((Ideal.absNorm p.asIdeal : ℂ) ^ (-w)) ^ Q.val.inertiaDeg (𝓞 K) =
      (Ideal.absNorm Q.val : ℂ) ^ (-w) := by
  rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul, ← Nat.cast_pow,
    Ideal.absNorm_pow_inertiaDeg (p := p.asIdeal) (q := Q.val)]

private noncomputable def primePowerUnit (x : ℂ) (hx : ‖x‖ < 1) (d : ℕ) : ℂˣ :=
  if hd : d = 0 then 1 else
    Units.mk0 ((1 - x ^ d)⁻¹) (inv_ne_zero <| sub_one_ne_zero_of_norm_lt_one <|
      by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx hd)

private theorem val_primePowerUnit (x : ℂ) (hx : ‖x‖ < 1) {d : ℕ} (hd : d ≠ 0) :
    (primePowerUnit x hx d : ℂ) = (1 - x ^ d)⁻¹ := by
  simp [primePowerUnit, hd]

private theorem val_localUnitProduct (p : HeightOneSpectrum (𝓞 K)) (w : ℂ)
    (hx : ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-w)‖ < 1) :
    (↑(∏ Q : p.asIdeal.primesOver (𝓞 M),
      primePowerUnit ((Ideal.absNorm p.asIdeal : ℂ) ^ (-w)) hx
        (Q.val.inertiaDeg (𝓞 K))) : ℂ) = (localDedekindDenominator M p w)⁻¹ := by
  change (Units.coeHom ℂ) (∏ Q : p.asIdeal.primesOver (𝓞 M),
    primePowerUnit ((Ideal.absNorm p.asIdeal : ℂ) ^ (-w)) hx (Q.val.inertiaDeg (𝓞 K))) = _
  simp only [map_prod, Units.coeHom_apply]
  rw [localDedekindDenominator, ← Finset.prod_inv_distrib]
  refine (Finset.prod_congr rfl ?_).trans
    (Finset.prod_subtype _ (fun _ ↦ IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 M)) _).symm
  intro Q _
  rw [val_primePowerUnit _ _ (Q.val.inertiaDeg_pos (𝓞 K)).ne', basePrime_pow_inertiaDeg]

private theorem split_integer_weight_product {α A : Type*} [Fintype α] [CommGroup A]
    (f : α → A) (a : α → ℤ) (b : A) (h : (∏ H, f H ^ a H) = b) :
    (∏ H, f H ^ (a H).toNat) = b * ∏ H, f H ^ (-a H).toNat := by
  rw [← h, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro H _
  have he : a H + ((-a H).toNat : ℤ) = ((a H).toNat : ℤ) := by omega
  rw [← zpow_natCast (f H) (a H).toNat, ← zpow_natCast (f H) (-a H).toNat, ← zpow_add, he]

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The integer weights give an identity of complex Euler factors after
negative weights are moved to the other side. -/
theorem exists_weighted_unramified_dedekind_local_product :
    ∃ a : CyclicSubgroups Gal(L/K) → ℤ,
      ∀ (p : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)),
        P.asIdeal.LiesOver p.asIdeal → Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal →
        ∀ w : ℂ, 0 < w.re →
          (∏ H : CyclicSubgroups Gal(L/K),
            (localDedekindDenominator (IntermediateField.fixedField H.val) p w)⁻¹ ^ (a H).toNat) =
          (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-w))⁻¹ ^ Nat.card Gal(L/K) *
            ∏ H : CyclicSubgroups Gal(L/K),
              (localDedekindDenominator (IntermediateField.fixedField H.val) p w)⁻¹ ^ (-a H).toNat := by
  classical
  obtain ⟨a, ha⟩ := exists_weighted_unramified_local_factor_product (K := K) (L := L)
  refine ⟨a, ?_⟩
  intro p P hP hu w hw
  let x := (Ideal.absNorm p.asIdeal : ℂ) ^ (-w)
  have hx : ‖x‖ < 1 := norm_neg_cpow_lt_one (absNorm_gt_one p.ne_bot) hw
  let u := primePowerUnit x hx
  let F : CyclicSubgroups Gal(L/K) → ℂˣ := fun H ↦
    ∏ Q : p.asIdeal.primesOver (𝓞 (IntermediateField.fixedField H.val)), u (Q.val.inertiaDeg (𝓞 K))
  have h : (∏ H, F H ^ a H) = u 1 ^ Nat.card Gal(L/K) := by
    simpa only [zpow_natCast] using ha p P hP hu u
  have hval (H : CyclicSubgroups Gal(L/K)) : (F H : ℂ) =
      (localDedekindDenominator (IntermediateField.fixedField H.val) p w)⁻¹ :=
    val_localUnitProduct _ p w hx
  have hbase : (u 1 : ℂ) = (1 - x)⁻¹ := by
    rw [val_primePowerUnit x hx (by decide : (1 : ℕ) ≠ 0), pow_one]
  have heq := congrArg (Units.coeHom ℂ) (split_integer_weight_product F a _ h)
  simpa only [map_prod, map_mul, map_pow, Units.coeHom_apply, hval, hbase] using heq

#check @exists_weighted_unramified_dedekind_local_product
#print axioms exists_weighted_unramified_dedekind_local_product

end FieldTarget
