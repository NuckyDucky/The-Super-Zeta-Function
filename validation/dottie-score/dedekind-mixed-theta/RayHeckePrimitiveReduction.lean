import RayHeckeStripCounts
import DedekindZetaZeroFree.Arithmetic.RayClasses.PrimitiveConductors.SexticSupport
import DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.RayCharacterFiniteCorrection

namespace FieldTarget

open DedekindZetaZeroFree DedekindZetaZeroFree.HeckeCorollary
open ArtinPrimitiveRootsConjecture IsDedekindDomain NumberField
open scoped NumberField

noncomputable section

/-- For a totally complex field, the primitive character of the same idelic
character recovers the continued reading off its possible pole. -/
theorem rayHeckeContinuation_eq_primitive_mul_euler
    (K : Type) [Field K] [NumberField K] (hc : IsTotallyComplex K)
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (ψ : RayClassCharacter K n),
      ψ.IsPrimitive ∧
      Set.EqOn (rayHeckeContinuation hm χ)
        (fun w ↦ rayHeckeContinuation hn ψ w *
          finiteEulerCorrection K ψ
            (RayClassBridge.narrowIdealModulus K m hm).finitePart.support w)
        ({1}ᶜ : Set ℂ) := by
  let Φ : IdeleClassGroup K →ₜ* ℂˣ :=
    ⟨RayClassBridge.ideleClassCharacter K hc m hm χ,
      RayClassBridge.ideleClassCharacter_continuous K hc m hm χ⟩
  obtain ⟨n, hn, _, ψ, hPrim, _, _, hSame, _⟩ :=
    PrimitiveRay.primitiveRay_exists hc Φ
      ⟨Nat.card (ClassFieldTheory.RayClassGroup (RayClassBridge.narrowIdealModulus K m hm)),
        RayClassBridge.ideleClassCharacter_exponent_pos K m hm,
        RayClassBridge.ideleClassCharacter_pow_card K hc m hm χ⟩
  let S := (RayClassBridge.narrowIdealModulus K m hm).finitePart.support
  have hSupport (p : HeightOneSpectrum (𝓞 K)) : p ∈ S ↔ m ≤ p.asIdeal := by
    simp only [S, ← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support, Set.mem_ofPred_eq]
  have hZero (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) : χ p.asIdeal = 0 := by
    apply (χ.eq_zero_iff' p.asIdeal).mpr
    exact Or.inr (by simpa only [sup_eq_left.mpr ((hSupport p).mp hp)] using p.isPrime.ne_top)
  have hAgree : ∀ p ∉ S, χ p.asIdeal = ψ p.asIdeal := by
    intro p hp
    have hNot : ¬ m ≤ p.asIdeal := fun h ↦ hp ((hSupport p).mpr h)
    have hNot' : ¬ n ≤ p.asIdeal :=
      PrimitiveRay.primitiveRay_support hc Φ n hn ψ hPrim hSame p
        (fun t ht ↦ RayClassBridge.ideleClassCharacter_finitePlaceIdeleClass_unit_of_not_dvd
          K hc m hm χ p hNot t ht)
    have hp' : p ∉ (RayClassBridge.narrowIdealModulus K n hn).finitePart.support := by
      simpa only [← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support,
        Set.mem_ofPred_eq] using hNot'
    let u := QuotientGroup.mk' (IdeleGroup.principalSubgroup K) (IdeleGroup.finitePrimeIdele p)
    have hu := congrArg (fun z : ℂˣ ↦ (z : ℂ)) (hSame u)
    exact (RayClassBridge.ideleClassCharacter_finitePrimeIdele K hc m hm χ p hp).symm.trans
      (hu.symm.trans (RayClassBridge.ideleClassCharacter_finitePrimeIdele K hc n hn ψ p hp'))
  refine ⟨n, hn, ψ, hPrim, ?_⟩
  apply rayHeckeContinuation_eqOn_of_right_match hm χ
    ((rayHeckeContinuation_differentiableOn hn ψ).mul
      (finiteEulerCorrection_differentiable K ψ S).differentiableOn)
  intro w hw
  change rayHeckeContinuation hm χ w =
    rayHeckeContinuation hn ψ w * finiteEulerCorrection K ψ S w
  rw [rayHeckeContinuation_eq_series hm χ hw, rayHeckeContinuation_eq_series hn ψ hw]
  exact rayCharacter_eulerCorrection K m n hm hn χ ψ S hZero hAgree w hw

/-- The correction is nonvanishing in the right half-plane, so the primitive
representative gives the same locations and multiplicities in the strip. -/
theorem rayHecke_exists_primitive_same_orders
    (K : Type) [Field K] [NumberField K] (hc : IsTotallyComplex K)
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (ψ : RayClassCharacter K n),
      ψ.IsPrimitive ∧ ∀ w : ℂ, 0 < w.re → w ≠ 1 →
        ((rayHeckeContinuation hm χ w = 0) ↔ (rayHeckeContinuation hn ψ w = 0)) ∧
        analyticOrderNatAt (rayHeckeContinuation hm χ) w =
          analyticOrderNatAt (rayHeckeContinuation hn ψ) w := by
  obtain ⟨n, hn, ψ, hPrim, hEq⟩ := rayHeckeContinuation_eq_primitive_mul_euler K hc m hm χ
  let S := (RayClassBridge.narrowIdealModulus K m hm).finitePart.support
  let C := finiteEulerCorrection K ψ S
  refine ⟨n, hn, ψ, hPrim, fun w hw hw1 ↦ ?_⟩
  have hC := finiteEulerCorrection_ne_zero K ψ
    (AbelianQuotient.rayCharacter_norm_le_one K n hn ψ) S w hw
  constructor
  · rw [hEq hw1, mul_eq_zero, or_iff_left hC]
  · have hψ := (rayHeckeContinuation_differentiableOn hn ψ).analyticOnNhd
      isOpen_compl_singleton w hw1
    have hAnalytic : AnalyticAt ℂ C w := (finiteEulerCorrection_differentiable K ψ S).analyticAt w
    have hNear : rayHeckeContinuation hm χ =ᶠ[nhds w] rayHeckeContinuation hn ψ * C :=
      Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hw1) fun _ hz ↦ hEq hz
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hNear, analyticOrderAt_mul hψ hAnalytic,
      hAnalytic.analyticOrderAt_eq_zero.mpr hC, add_zero]

theorem rayHecke_exists_primitive_same_counts
    (K : Type) [Field K] [NumberField K] (hc : IsTotallyComplex K)
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (ψ : RayClassCharacter K n),
      ψ.IsPrimitive ∧ ∀ (T : ℝ) (P : ℂ → Prop),
        (rayHeckeCountingFunction hm χ).stripZeroCount T P =
          (rayHeckeCountingFunction hn ψ).stripZeroCount T P := by
  classical
  obtain ⟨n, hn, ψ, hPrim, hSame⟩ := rayHecke_exists_primitive_same_orders K hc m hm χ
  let f := rayHeckeCountingFunction hm χ
  let g := rayHeckeCountingFunction hn ψ
  have hNe {w : ℂ} (hw : w.re < 1) : w ≠ 1 := by
    rintro rfl
    exact lt_irrefl _ hw
  refine ⟨n, hn, ψ, hPrim, fun T P ↦ ?_⟩
  change f.stripZeroCount T P = g.stripZeroCount T P
  have hZeros : f.stripZeros T = g.stripZeros T := by
    ext w
    simp only [NonzeroEntireFunction.mem_stripZeros]
    apply and_congr_right
    intro hlo
    apply and_congr_right
    intro hhi
    apply and_congr_right
    intro _
    rw [show f w = 0 ↔ rayHeckeContinuation hm χ w = 0 from
      rayHeckeCountingFunction_zero_iff hm χ (hNe hhi),
      show g w = 0 ↔ rayHeckeContinuation hn ψ w = 0 from
      rayHeckeCountingFunction_zero_iff hn ψ (hNe hhi)]
    exact (hSame w hlo (hNe hhi)).1
  simp only [NonzeroEntireFunction.stripZeroCount, hZeros]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  obtain ⟨hlo, hhi, _, _⟩ := (g.mem_stripZeros T w).mp (Finset.mem_filter.mp hw).1
  rw [show analyticOrderNatAt f.toFun w = analyticOrderNatAt (rayHeckeContinuation hm χ) w from
        rayHeckeCountingFunction_order_eq hm χ (hNe hhi),
      show analyticOrderNatAt g.toFun w = analyticOrderNatAt (rayHeckeContinuation hn ψ) w from
        rayHeckeCountingFunction_order_eq hn ψ (hNe hhi)]
  exact (hSame w hlo (hNe hhi)).2

#check @rayHecke_exists_primitive_same_orders
#check @rayHecke_exists_primitive_same_counts
#print axioms rayHeckeContinuation_eq_primitive_mul_euler
#print axioms rayHecke_exists_primitive_same_orders
#print axioms rayHecke_exists_primitive_same_counts

end
end FieldTarget
