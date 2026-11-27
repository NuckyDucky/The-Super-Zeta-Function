import DedekindCyclicZetaLocal
import DedekindFiniteRamification
import DedekindZetaZeroFree.LFunctions.Dedekind.EulerProductRegrouping
import FieldTarget

namespace FieldTarget

open Complex ArtinPrimitiveRootsConjecture IsDedekindDomain
open scoped NumberField BigOperators Classical

variable {K : Type*} [Field K] [NumberField K]
variable (M : Type*) [Field M] [NumberField M] [Algebra K M]

/-- The denominator factors at the omitted base primes. -/
noncomputable def finiteEulerCorrection
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : ℂ) : ℂ :=
  ∏ p ∈ S, localDedekindDenominator M p w

theorem finiteEulerCorrection_ne_zero
    (S : Finset (HeightOneSpectrum (𝓞 K))) {w : ℂ} (hw : 0 < w.re) :
    finiteEulerCorrection M S w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ ↦ localDedekindDenominator_ne_zero M p hw

theorem differentiable_finiteEulerCorrection (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (finiteEulerCorrection M S) :=
  Differentiable.fun_finsetProd fun p _ ↦ differentiable_localDedekindDenominator M p

/-- Omitting a finite set of base primes multiplies the ordinary Dedekind
zeta by the product of their Euler denominators in the half-plane of convergence. -/
theorem hasProd_dedekind_euler_outside_finset
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : ℂ) (hw : 1 < w.re) :
    HasProd (fun p : HeightOneSpectrum (𝓞 K) ↦
      if p ∈ S then 1 else (localDedekindDenominator M p w)⁻¹)
      (finiteEulerCorrection M S w * NumberField.dedekindZeta M w) := by
  classical
  let d (p : HeightOneSpectrum (𝓞 K)) := localDedekindDenominator M p w
  let g (p : HeightOneSpectrum (𝓞 K)) := if p ∈ S then d p else 1
  have hprod : HasProd (fun p ↦ (d p)⁻¹) (NumberField.dedekindZeta M w) := by
    simpa only [d, localDedekindDenominator, Finset.prod_inv_distrib] using
      DedekindZetaZeroFree.AbelianQuotient.primeEulerRegroup K M w hw
  have hfinite : HasProd g (∏ p ∈ S, g p) :=
    hasProd_prod_of_ne_finset_one (s := S) (fun p hp ↦ by simp [g, hp])
  have heq : (∏ p ∈ S, g p) = finiteEulerCorrection M S w := by
    exact Finset.prod_congr rfl fun p hp ↦ ite_eq_left hp
  rw [heq] at hfinite
  refine (hfinite.mul hprod).congr_fun fun p ↦ ?_
  by_cases hp : p ∈ S
  · have hd := localDedekindDenominator_ne_zero M p (zero_lt_one.trans hw)
    simp [g, d, hp, mul_inv_cancel₀ hd]
  · simp [g, d, hp]

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- Clearing the weights and the finitely many ramified factors gives an
identity of continued Dedekind zeta products at every input off the pole. -/
theorem exists_cyclic_fixed_field_zeta_product
    {ZK : ℂ → ℂ} (hK : IsDedekindZeta K ZK)
    {ZE : CyclicSubgroups Gal(L/K) → ℂ → ℂ}
    (hE : ∀ H, IsDedekindZeta (IntermediateField.fixedField H.val) (ZE H)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : CyclicSubgroups Gal(L/K) → ℤ),
      (∀ p, p ∈ S ↔ ∃ P : HeightOneSpectrum (𝓞 L),
        P.asIdeal.LiesOver p.asIdeal ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal) ∧
      ∀ w : ℂ, w ≠ 1 →
        (∏ H : CyclicSubgroups Gal(L/K),
          (finiteEulerCorrection (IntermediateField.fixedField H.val) S w * ZE H w) ^
            (a H).toNat) =
          (finiteEulerCorrection K S w * ZK w) ^ Nat.card Gal(L/K) *
            ∏ H : CyclicSubgroups Gal(L/K),
              (finiteEulerCorrection (IntermediateField.fixedField H.val) S w * ZE H w) ^
                (-a H).toNat := by
  classical
  obtain ⟨S, hS⟩ := exists_ramified_base_prime_finset K L
  obtain ⟨a, ha⟩ := exists_weighted_unramified_dedekind_local_product (K := K) (L := L)
  let E := fun H : CyclicSubgroups Gal(L/K) ↦ IntermediateField.fixedField H.val
  let B (w : ℂ) := finiteEulerCorrection K S w * ZK w
  let F (H : CyclicSubgroups Gal(L/K)) (w : ℂ) := finiteEulerCorrection (E H) S w * ZE H w
  let left (w : ℂ) := ∏ H, F H w ^ (a H).toNat
  let right (w : ℂ) := B w ^ Nat.card Gal(L/K) * ∏ H, F H w ^ (-a H).toNat
  have hconv (w : ℂ) (hw : 1 < w.re) : left w = right w := by
    let f (H : CyclicSubgroups Gal(L/K)) (p : HeightOneSpectrum (𝓞 K)) :=
      if p ∈ S then 1 else (localDedekindDenominator (E H) p w)⁻¹
    let b (p : HeightOneSpectrum (𝓞 K)) :=
      if p ∈ S then 1 else (localDedekindDenominator K p w)⁻¹
    have hB : HasProd b (B w) := by
      simpa only [B, hK.2 w hw] using hasProd_dedekind_euler_outside_finset K S w hw
    have hF (H : CyclicSubgroups Gal(L/K)) : HasProd (f H) (F H w) := by
      simpa only [F, (hE H).2 w hw] using hasProd_dedekind_euler_outside_finset (E H) S w hw
    have hleft : HasProd (fun p ↦ ∏ H, f H p ^ (a H).toNat) (left w) :=
      hasProd_prod fun H _ ↦ (hF H).pow _
    have hright : HasProd (fun p ↦ b p ^ Nat.card Gal(L/K) *
        ∏ H, f H p ^ (-a H).toNat) (right w) :=
      (hB.pow _).mul (hasProd_prod fun H _ ↦ (hF H).pow _)
    refine (hleft.congr_fun fun p ↦ ?_).unique hright
    by_cases hp : p ∈ S
    · simp [f, b, hp]
    obtain ⟨U⟩ := Ideal.nonempty_primesOver (R := 𝓞 K) (S := 𝓞 L) p.asIdeal
    let P : HeightOneSpectrum (𝓞 L) :=
      ⟨U.val, U.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot U.property⟩
    have hP : P.asIdeal.LiesOver p.asIdeal := U.property.2
    have hu : Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
      by_contra h
      exact hp ((hS p).mpr ⟨P, hP, h⟩)
    simpa only [f, b, E, ite_eq_right hp, localDedekindDenominator_self] using
      (ha p P hP hu w (zero_lt_one.trans hw)).symm
  have hBdiff : DifferentiableOn ℂ B ({1}ᶜ : Set ℂ) :=
    (differentiable_finiteEulerCorrection K S).differentiableOn.mul hK.1
  have hFdiff (H : CyclicSubgroups Gal(L/K)) : DifferentiableOn ℂ (F H) ({1}ᶜ : Set ℂ) :=
    (differentiable_finiteEulerCorrection (E H) S).differentiableOn.mul (hE H).1
  have hleft : DifferentiableOn ℂ left ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.fun_finsetProd fun H _ ↦ (hFdiff H).pow _
  have hright : DifferentiableOn ℂ right ({1}ᶜ : Set ℂ) :=
    (hBdiff.pow _).mul (DifferentiableOn.fun_finsetProd fun H _ ↦ (hFdiff H).pow _)
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have htwo : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hnear : left =ᶠ[nhds (2 : ℂ)] right :=
    Filter.eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re))
      fun w hw ↦ hconv w hw
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hleft.analyticOnNhd isOpen_compl_singleton) (hright.analyticOnNhd isOpen_compl_singleton)
    hconn htwo hnear
  exact ⟨S, a, hS, fun _ hw ↦ heq hw⟩

#check @exists_cyclic_fixed_field_zeta_product
#print axioms finiteEulerCorrection_ne_zero
#print axioms hasProd_dedekind_euler_outside_finset
#print axioms exists_cyclic_fixed_field_zeta_product

end FieldTarget
