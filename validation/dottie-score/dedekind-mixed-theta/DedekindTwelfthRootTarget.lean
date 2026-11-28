import DedekindSevenEighthsCoverage
import RayHeckePrimitiveReduction
import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthCyclotomicExtension

namespace FieldTarget

open ArtinPrimitiveRootsConjecture DedekindZetaZeroFree
open scoped NumberField

/-- Adjoining a primitive twelfth root multiplies the base continuation by
an entire function of the same complex input. -/
theorem mixedThetaContinuation_cyclotomic12_factor (K : Type) [Field K] [NumberField K] :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ w : ℂ, w ≠ 1 →
        mixedThetaContinuation (CyclotomicField 12 K) w = g w * mixedThetaContinuation K w := by
  let E := CyclotomicField 12 K
  obtain ⟨hGal, hComm, _, _⟩ := cyclotomic12_context K
  let : IsGalois K E := hGal
  obtain ⟨fK, fE, g, hKd, hEd, hg, hKs, hEs, hProduct⟩ :=
    dedekindAbelianQuotient K E hComm
  refine ⟨g, hg, fun w hw ↦ ?_⟩
  change mixedThetaContinuation E w = g w * mixedThetaContinuation K w
  rw [continuation_eq_off_one (mixedThetaContinuation_isDedekind E) ⟨hEd, hEs⟩ hw,
      continuation_eq_off_one (mixedThetaContinuation_isDedekind K) ⟨hKd, hKs⟩ hw]
  exact hProduct w hw

theorem mixedThetaContinuation_cyclotomic12_order_ge (K : Type) [Field K] [NumberField K]
    {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt (mixedThetaContinuation K) w ≤
      analyticOrderAt (mixedThetaContinuation (CyclotomicField 12 K)) w := by
  obtain ⟨g, hg, heq⟩ := mixedThetaContinuation_cyclotomic12_factor K
  have hNear : mixedThetaContinuation (CyclotomicField 12 K) =ᶠ[nhds w]
      g * mixedThetaContinuation K :=
    Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hw) fun _ hz ↦ heq _ hz
  have hK := (mixedThetaContinuation_isDedekind K).1.analyticOnNhd
    isOpen_compl_singleton w hw
  rw [analyticOrderAt_congr hNear, analyticOrderAt_mul (hg.analyticAt w) hK, add_comm]
  exact le_self_add

/-- A complete count on the line in the extension certifies the base field
through the same height. -/
theorem mixedTheta_cyclotomic12_stripCounts_equal_descend
    (K : Type) [Field K] [NumberField K] (T : ℝ)
    (hE : (mixedThetaCountingFunction (CyclotomicField 12 K)).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction (CyclotomicField 12 K)).stripZeroCount T (fun w ↦ w.re = 1 / 2)) :
    (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  let E := CyclotomicField 12 K
  obtain ⟨g, _, hFactor⟩ := mixedThetaContinuation_cyclotomic12_factor K
  apply ((mixedThetaCountingFunction K).stripCounts_equal_iff T).mpr
  intro w hlo hhi hT hZero
  have hne : w ≠ 1 := by
    rintro rfl
    exact lt_irrefl _ hhi
  have hBase := (mixedThetaEntireReading_zero_iff K w hlo hhi).mp hZero
  have hUpper : mixedThetaCountingFunction E w = 0 :=
    (mixedThetaEntireReading_zero_iff E w hlo hhi).mpr (by rw [hFactor w hne, hBase, mul_zero])
  exact ((mixedThetaCountingFunction E).stripCounts_equal_iff T).mp hE w hlo hhi hT hUpper

theorem dedekindZetaRH_of_galois_twelfthRoot_fields
    (h : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      (∃ ζ : L, IsPrimitiveRoot ζ 12) → DedekindZetaRH L)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  refine dedekindZetaRH_of_all_galois_over_rat (fun F _ _ _ ↦ ?_) K
  let E := CyclotomicField 12 F
  let L := RationalNormalClosure E
  let ι : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
  obtain ⟨hGal, _, _, ζ, hζ, _⟩ := cyclotomic12_context F
  let : IsGalois F E := hGal
  have hL : DedekindZetaRH L := h L ⟨ι ζ, hζ.map_of_injective ι.injective⟩
  exact dedekindZetaRH_of_galois_extension F E
    (dedekindZetaRH_of_rational_normalClosure E hL)

/-- It suffices to check the same right-half band on rational Galois fields
containing a primitive twelfth root. -/
theorem allDedekindRH_iff_galois_twelfthRoot_band :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
        (∃ ζ : L, IsPrimitiveRoot ζ 12) → ∀ w : ℂ,
          1 / 2 < w.re → w.re ≤ 7 / 8 → 0 ≤ w.im →
            mixedThetaContinuation L w ≠ 0 := by
  constructor
  · intro h L _ _ _ _
    exact (dedekindZetaRH_iff_seven_eighths_nonnegative_band L).mp (h L)
  · intro h K _ _
    refine dedekindZetaRH_of_galois_twelfthRoot_fields (fun L _ _ _ hζ ↦ ?_) K
    exact (dedekindZetaRH_iff_seven_eighths_nonnegative_band L).mpr (h L hζ)

/-- On these fields the primitive ray readings are sufficient
for every ray reading on the same band, at the same complex input. -/
theorem allDedekindRH_iff_galois_twelfthRoot_primitive_band :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
        (∃ ζ : L, IsPrimitiveRoot ζ 12) →
          ∀ (m : Ideal (𝓞 L)) (hm : m ≠ ⊥) (χ : RayClassCharacter L m),
            χ.IsPrimitive → ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 7 / 8 →
              0 ≤ w.im → rayHeckeContinuation hm χ w ≠ 0 := by
  constructor
  · intro h L _ _ _ _ m hm χ _ w hlo hhi _
    exact allDedekindRH_iff_rayHecke_seven_eighths_band.mp h L m hm χ w hlo hhi
  · intro h
    apply allDedekindRH_iff_galois_twelfthRoot_band.mpr
    intro L _ _ _ hζ w hlo hhi ht hz
    obtain ⟨ζ, hRoot⟩ := hζ
    have hc := primitive12_totallyComplex L ζ hRoot
    have hNe : w ≠ 1 := by
      rintro rfl
      norm_num at hhi
    let χ := LargeSieve.principalUnitRayCharacter L
    obtain ⟨m, hm, ψ, hPrim, hSame⟩ :=
      rayHecke_exists_primitive_same_orders L hc ⊤ top_ne_bot χ
    have hχ : rayHeckeContinuation top_ne_bot χ w = 0 := by
      rw [continuation_eq_off_one (unitRayHecke_isDedekind L)
        (mixedThetaContinuation_isDedekind L) hNe]
      exact hz
    exact h L ⟨ζ, hRoot⟩ m hm ψ hPrim w hlo hhi ht
      ((hSame w (by linarith only [hlo]) hNe).1.mp hχ)

/-- Combine the reduced field family with the existing Dottie sample
criterion. The Dirichlet input discharges the abelian members. -/
theorem dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_samples
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hCover : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      (∃ ζ : L, IsPrimitiveRoot ζ 12) → ¬ IsAbelianGalois ℚ L →
        HasDottieCompletedSamplesToSevenEighths L)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  refine dedekindZetaRH_of_galois_twelfthRoot_fields (fun L _ _ _ hζ ↦ ?_) K
  by_cases hA : IsAbelianGalois ℚ L
  · let : IsAbelianGalois ℚ L := hA
    exact dedekindZetaRH_of_dirichlet_of_abelian hD L
  · exact dedekindZetaRH_of_completed_samples_to_seven_eighths L (hCover L hζ hA)

#check @allDedekindRH_iff_galois_twelfthRoot_primitive_band
#check @dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_samples
#check @mixedTheta_cyclotomic12_stripCounts_equal_descend
#print axioms mixedThetaContinuation_cyclotomic12_factor
#print axioms mixedThetaContinuation_cyclotomic12_order_ge
#print axioms mixedTheta_cyclotomic12_stripCounts_equal_descend
#print axioms dedekindZetaRH_of_galois_twelfthRoot_fields
#print axioms allDedekindRH_iff_galois_twelfthRoot_band
#print axioms allDedekindRH_iff_galois_twelfthRoot_primitive_band
#print axioms dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_samples

end FieldTarget
