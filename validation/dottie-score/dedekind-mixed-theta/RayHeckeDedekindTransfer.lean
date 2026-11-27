import RayHeckeStripCounts
import DedekindAbelianFields
import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.RayCharacterGaloisRealization
import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ConductorRealization
import DedekindZetaZeroFree.LFunctions.Dedekind.GaloisCharacterFactorization
import DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.RayCharacterFiniteCorrection

/-! Transfer between Dedekind zeta and the actual finite-order ray-class
Hecke functions at the same complex point. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex IsDedekindDomain Set
open DedekindZetaZeroFree DedekindZetaZeroFree.AbelianQuotient DedekindZetaZeroFree.HeckeCorollary
open scoped NumberField BigOperators ComplexConjugate

noncomputable section

private instance galoisCommGroup (K E : Type) [Field K] [Field E] [Algebra K E]
    [IsAbelianGalois K E] : CommGroup (E ≃ₐ[K] E) :=
  { (inferInstance : Group (E ≃ₐ[K] E)) with mul_comm := fun σ τ ↦ mul_comm' σ τ }

theorem dedekindContinuation_eq_rayHecke_product_of_local_factors
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (m : ComplexDual (E ≃ₐ[K] E) → Ideal (𝓞 K))
    (χ : (ρ : ComplexDual (E ≃ₐ[K] E)) → RayClassCharacter K (m ρ))
    (hm : ∀ ρ, m ρ ≠ ⊥)
    (hprime : ∀ (ρ : ComplexDual (E ≃ₐ[K] E))
      (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 E)),
      W.asIdeal.LiesOver p.asIdeal → χ ρ p.asIdeal = primeArtinValue ρ W)
    {w : ℂ} (hw : w ≠ 1) :
    mixedThetaContinuation E w =
      ∏ ρ : ComplexDual (E ≃ₐ[K] E), rayHeckeContinuation (hm ρ) (χ ρ) w := by
  let F (z : ℂ) := ∏ ρ : ComplexDual (E ≃ₐ[K] E), rayHeckeContinuation (hm ρ) (χ ρ) z
  have hF : IsDedekindZeta E F := by
    constructor
    · exact DifferentiableOn.fun_finsetProd (fun ρ _ ↦
        rayHeckeContinuation_differentiableOn (hm ρ) (χ ρ))
    · intro z hz
      dsimp [F]
      simp_rw [rayHeckeContinuation_eq_series _ _ hz]
      exact (allCharacterFactorization K E m χ hm hprime z hz).symm
  exact continuation_eq_off_one (mixedThetaContinuation_isDedekind E) hF hw

/-- For each ray character there is one number field which receives its
critical-strip zeros. The finite Euler corrections preserve the same input. -/
theorem rayHecke_zero_lifts_to_dedekind
    (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ R : ClassFieldTheory.RayClassFieldRealization K (narrowIdealModulus K m hm),
      ∀ w : ℂ, 0 < w.re → w ≠ 1 → rayHeckeContinuation hm χ w = 0 →
        mixedThetaContinuation R.extension w = 0 := by
  obtain ⟨R, ρ, _, hρprime⟩ := exists_rayCharacter_galoisRealization K m hm χ
  obtain ⟨m₀, χ₀, hm₀, _, _, _, hprime⟩ := conductorRayRealization K R.extension
  let S := (narrowIdealModulus K m hm).finitePart.support
  have hzero : ∀ p ∈ S, χ p.asIdeal = 0 :=
    rayCharacter_eq_zero_of_mem_modulus_support K m hm χ
  have hagree : ∀ p ∉ S, χ p.asIdeal = χ₀ ρ p.asIdeal := by
    intro p hp
    obtain ⟨Q⟩ := Ideal.nonempty_primesOver (R := 𝓞 K) (S := 𝓞 R.extension) p.asIdeal
    let W : HeightOneSpectrum (𝓞 R.extension) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩
    exact (hρprime p hp W Q.2.2).trans (hprime ρ p W Q.2.2).symm
  have hFactor : Set.EqOn (rayHeckeContinuation hm χ)
      (fun z ↦ rayHeckeContinuation (hm₀ ρ) (χ₀ ρ) z *
        finiteEulerCorrection K (χ₀ ρ) S z) ({1}ᶜ : Set ℂ) := by
    apply rayHeckeContinuation_eqOn_of_right_match hm χ
      ((rayHeckeContinuation_differentiableOn (hm₀ ρ) (χ₀ ρ)).mul
        (finiteEulerCorrection_differentiable K (χ₀ ρ) S).differentiableOn)
    intro z hz
    change rayHeckeContinuation hm χ z =
      rayHeckeContinuation (hm₀ ρ) (χ₀ ρ) z * finiteEulerCorrection K (χ₀ ρ) S z
    rw [rayHeckeContinuation_eq_series hm χ hz,
      rayHeckeContinuation_eq_series (hm₀ ρ) (χ₀ ρ) hz]
    exact rayCharacter_eulerCorrection K m (m₀ ρ) hm (hm₀ ρ) χ (χ₀ ρ) S hzero hagree z hz
  refine ⟨R, ?_⟩
  intro w hlo hw hz
  have hCorrection := finiteEulerCorrection_ne_zero K (χ₀ ρ)
    (rayCharacter_norm_le_one K (m₀ ρ) (hm₀ ρ) (χ₀ ρ)) S w hlo
  have hz₀ := (mul_eq_zero.mp ((hFactor hw).symm.trans hz)).resolve_right hCorrection
  rw [dedekindContinuation_eq_rayHecke_product_of_local_factors K R.extension m₀ χ₀ hm₀ hprime hw]
  exact Finset.prod_eq_zero (Finset.mem_univ ρ) hz₀

theorem rayHecke_zero_reflects_into_family
    (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (χ : RayClassCharacter K m) {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1) (hz : rayHeckeContinuation hm χ w = 0) :
    ∃ (m' : Ideal (𝓞 K)) (hm' : m' ≠ ⊥) (χ' : RayClassCharacter K m'),
      rayHeckeContinuation hm' χ' (1 - conj w) = 0 := by
  obtain ⟨R, hLift⟩ := rayHecke_zero_lifts_to_dedekind K m hm χ
  have hw : w ≠ 1 := fun he ↦ by
    rw [he, Complex.one_re] at hhi
    exact (lt_irrefl _ hhi)
  have hw' : 1 - conj w ≠ 1 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h
    linarith only [h, hlo]
  have hZero := mixedThetaContinuation_reflects R.extension w hlo hhi (hLift w hlo hw hz)
  obtain ⟨m', χ', hm', _, _, _, hPrime⟩ := conductorRayRealization K R.extension
  rw [dedekindContinuation_eq_rayHecke_product_of_local_factors K R.extension
    m' χ' hm' hPrime hw'] at hZero
  obtain ⟨ρ, _, hρ⟩ := Finset.prod_eq_zero_iff.mp hZero
  exact ⟨m' ρ, hm' ρ, χ' ρ, hρ⟩

theorem allDedekindRH_iff_all_rayHeckeRH :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
        (hm : m ≠ ⊥) (χ : RayClassCharacter K m),
        StripZerosOnLine (rayHeckeContinuation hm χ) := by
  constructor
  · intro h K _ _ m hm χ w hlo hhi hz
    obtain ⟨R, hLift⟩ := rayHecke_zero_lifts_to_dedekind K m hm χ
    have hw : w ≠ 1 := fun he ↦ by rw [he, Complex.one_re] at hhi; exact (lt_irrefl _ hhi)
    exact h R.extension (mixedThetaContinuation R.extension)
      (mixedThetaContinuation_isDedekind R.extension) w hlo hhi (hLift w hlo hw hz)
  · intro h K _ _
    exact (dedekindZetaRH_iff_unit_rayHecke K).mpr
      (h K ⊤ top_ne_bot (LargeSieve.principalUnitRayCharacter K))

/-- The rational Dirichlet theorem supplies every rational ray-character
case by the abelian extension attached to that character. -/
theorem rational_rayHeckeRH_of_dirichlet
    (hD : ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), StripZerosOnLine ψ.LFunction)
    (m : Ideal (𝓞 ℚ)) (hm : m ≠ ⊥) (χ : RayClassCharacter ℚ m) :
    StripZerosOnLine (rayHeckeContinuation hm χ) := by
  obtain ⟨R, hLift⟩ := rayHecke_zero_lifts_to_dedekind ℚ m hm χ
  intro w hlo hhi hz
  have hw : w ≠ 1 := fun he ↦ by rw [he, Complex.one_re] at hhi; exact (lt_irrefl _ hhi)
  exact dedekindZetaRH_of_dirichlet_of_abelian hD R.extension
    (mixedThetaContinuation R.extension) (mixedThetaContinuation_isDedekind R.extension)
    w hlo hhi (hLift w hlo hw hz)

theorem rayHecke_familyRH_iff_right_band (K : Type) [Field K] [NumberField K] :
    (∀ (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m),
      StripZerosOnLine (rayHeckeContinuation hm χ)) ↔
      ∀ (m : Ideal (𝓞 K))
        (hm : m ≠ ⊥) (χ : RayClassCharacter K m) (w : ℂ),
        1 / 2 < w.re → w.re ≤ 31 / 32 → rayHeckeContinuation hm χ w ≠ 0 := by
  constructor
  · intro h m hm χ w hlo hhi hz
    have hLine := h m hm χ w (by linarith only [hlo]) (by linarith only [hhi]) hz
    exact (ne_of_gt hlo) hLine
  · intro h m hm χ w hlo hhi hz
    have hRight {n : Ideal (𝓞 K)} (hn : n ≠ ⊥) (ψ : RayClassCharacter K n)
        (z : ℂ) (hzlo : 1 / 2 < z.re) (hzhi : z.re < 1) :
        rayHeckeContinuation hn ψ z ≠ 0 := by
      have hz₁ : z ≠ 1 := fun he ↦ by
        rw [he, Complex.one_re] at hzhi
        exact (lt_irrefl _ hzhi)
      by_cases hBand : z.re ≤ 31 / 32
      · exact h n hn ψ z hzlo hBand
      · exact rayHeckeContinuation_ne_zero_of_right_edge hn ψ (lt_of_not_ge hBand) hz₁
    rcases lt_trichotomy w.re (1 / 2 : ℝ) with hl | he | hr
    · obtain ⟨n, hn, ψ, hReflected⟩ := rayHecke_zero_reflects_into_family K m hm χ hlo hhi hz
      have hRe : (1 - conj w).re = 1 - w.re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      have hLeft : 1 / 2 < (1 - conj w).re := by
        rw [hRe]
        linarith only [hl]
      have hUpper : (1 - conj w).re < 1 := by
        rw [hRe]
        linarith only [hlo]
      exact (hRight hn ψ (1 - conj w) hLeft hUpper hReflected).elim
    · exact he
    · exact (hRight hm χ w hr hhi hz).elim

theorem allDedekindRH_iff_rayHecke_right_band :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
        (hm : m ≠ ⊥) (χ : RayClassCharacter K m) (w : ℂ),
        1 / 2 < w.re → w.re ≤ 31 / 32 → rayHeckeContinuation hm χ w ≠ 0 := by
  rw [allDedekindRH_iff_all_rayHeckeRH]
  constructor
  · intro h K _ _
    exact (rayHecke_familyRH_iff_right_band K).mp (h K)
  · intro h K _ _
    exact (rayHecke_familyRH_iff_right_band K).mpr (h K)

#check @rayHecke_zero_lifts_to_dedekind
#check @rayHecke_zero_reflects_into_family
#check @allDedekindRH_iff_all_rayHeckeRH
#check @rational_rayHeckeRH_of_dirichlet
#check @rayHecke_familyRH_iff_right_band
#check @allDedekindRH_iff_rayHecke_right_band
#print axioms dedekindContinuation_eq_rayHecke_product_of_local_factors
#print axioms rayHecke_zero_lifts_to_dedekind
#print axioms rayHecke_zero_reflects_into_family
#print axioms allDedekindRH_iff_all_rayHeckeRH
#print axioms rational_rayHeckeRH_of_dirichlet
#print axioms rayHecke_familyRH_iff_right_band
#print axioms allDedekindRH_iff_rayHecke_right_band

end
end FieldTarget
