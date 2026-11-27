import RayHeckeRightBand
import HeckeSevenEighthsSolution

/-! Use Hu's unitary Hecke theorem for the trivial idèle class character.
The resulting bound passes through the existing same-point zero lift to all
ray-class characters, including those with finite Euler corrections. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex NumberField IsDedekindDomain
open DedekindZetaZeroFree UniqueFactorizationMonoid
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem hecke_trivial_primeValue (v : HeightOneSpectrum (𝓞 K)) :
    HeckeSevenEighths.primeValue (1 : HeckeSevenEighths.HeckeCharacter K) v = 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hVal : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.adicCompletion.valued_coe K v π).trans hπ
  have hπ₀ : (π : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hVal WithZero.coe_ne_zero)
  have h : HeckeSevenEighths.IsUnramifiedAt (1 : HeckeSevenEighths.HeckeCharacter K) v ∧
      ∃ ϖ : (v.adicCompletion K)ˣ,
        Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    refine ⟨fun _ _ ↦ rfl, Units.mk0 π hπ₀, ?_⟩
    exact hVal
  rw [HeckeSevenEighths.primeValue, dite_eq_left h]
  exact Circle.coe_one

theorem hecke_trivial_coeff_eq_principal (I : Ideal (𝓞 K)) :
    HeckeSevenEighths.coeff (1 : HeckeSevenEighths.HeckeCharacter K) I =
      LargeSieve.principalUnitRayCharacter K I := by
  rw [HeckeSevenEighths.coeff, LargeSieve.principalUnitRayCharacter_apply]
  by_cases hI : I = ⊥
  · simp only [ite_eq_left hI]
  · simp only [ite_eq_right hI]
    calc
      _ = ((normalizedFactors I).map fun _ ↦ (1 : ℂ)).prod := by
        congr 1
        apply Multiset.map_congr rfl
        intro P hP
        have hp : Prime P := prime_of_normalized_factor P hP
        rw [dite_eq_left (show P.IsPrime ∧ P ≠ ⊥ from ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩)]
        exact hecke_trivial_primeValue _
      _ = 1 := Multiset.prod_map_one

theorem mixedThetaContinuation_ne_zero_above_seven_eighths
    (K : Type) [Field K] [NumberField K] {w : ℂ}
    (hlo : 7 / 8 < w.re) (hhi : w.re < 1) : mixedThetaContinuation K w ≠ 0 := by
  obtain ⟨f, P, hP, hf, hPole, hSeries, hNonzero⟩ := HeckeSevenEighths.heckeL_zeroFree K 1
  have hMatch (z : ℂ) (hz : 1 < z.re) : f z = NumberField.dedekindZeta K z := by
    have h := (hSeries z hz).tsum_eq.symm
    simp_rw [hecke_trivial_coeff_eq_principal] at h
    exact h.trans (PrincipalPointwise.principal_top_series_eq_dedekindZeta K
      (LargeSieve.principalUnitRayCharacter K)
      (LargeSieve.principalUnitRayCharacter_isPrincipal K) z hz)
  rw [← eq_mixedThetaContinuation_of_right_match K hP.finite (fun p hp ↦ (hPole p hp).1)
    hf hMatch hhi]
  exact hNonzero w hlo (fun hp ↦ (ne_of_lt hhi) (hPole w hp).1)

theorem rayHeckeContinuation_ne_zero_above_seven_eighths
    (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (χ : RayClassCharacter K m) {w : ℂ}
    (hlo : 7 / 8 < w.re) (hhi : w.re < 1) : rayHeckeContinuation hm χ w ≠ 0 :=
  rayHeckeContinuation_ne_zero_of_dedekind K m hm χ (by linarith only [hlo]) hhi
    (fun E _ _ ↦ mixedThetaContinuation_ne_zero_above_seven_eighths E hlo hhi)

theorem allDedekindRH_iff_rayHecke_seven_eighths_band :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
        (hm : m ≠ ⊥) (χ : RayClassCharacter K m) (w : ℂ),
        1 / 2 < w.re → w.re ≤ 7 / 8 → rayHeckeContinuation hm χ w ≠ 0 :=
  allDedekindRH_iff_rayHecke_right_band_of_dedekind_edge (by norm_num)
    (fun K _ _ _ hlo hhi ↦ mixedThetaContinuation_ne_zero_above_seven_eighths K hlo hhi)

theorem allDedekindRH_iff_mixedTheta_seven_eighths_band :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (K : Type) [Field K] [NumberField K] (w : ℂ),
        1 / 2 < w.re → w.re ≤ 7 / 8 → mixedThetaContinuation K w ≠ 0 := by
  constructor
  · intro h K _ _ w hlo hhi hz
    have hLine := h K (mixedThetaContinuation K) (mixedThetaContinuation_isDedekind K) w
      (by linarith only [hlo]) (by linarith only [hhi]) hz
    exact (ne_of_gt hlo) hLine
  · intro h
    apply allDedekindRH_iff_rayHecke_seven_eighths_band.mpr
    intro K _ _ m hm χ w hlo hhi
    exact rayHeckeContinuation_ne_zero_of_dedekind K m hm χ
      (by linarith only [hlo]) (by linarith only [hhi]) (fun E _ _ ↦ h E w hlo hhi)

#check @mixedThetaContinuation_ne_zero_above_seven_eighths
#check @rayHeckeContinuation_ne_zero_above_seven_eighths
#check @allDedekindRH_iff_rayHecke_seven_eighths_band
#check @allDedekindRH_iff_mixedTheta_seven_eighths_band
#print axioms HeckeSevenEighths.heckeL_zeroFree
#print axioms hecke_trivial_coeff_eq_principal
#print axioms mixedThetaContinuation_ne_zero_above_seven_eighths
#print axioms rayHeckeContinuation_ne_zero_above_seven_eighths
#print axioms allDedekindRH_iff_rayHecke_seven_eighths_band
#print axioms allDedekindRH_iff_mixedTheta_seven_eighths_band

end FieldTarget
