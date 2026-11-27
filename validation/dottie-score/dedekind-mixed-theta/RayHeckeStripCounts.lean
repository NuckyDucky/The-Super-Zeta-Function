import DedekindFiniteStripCounts
import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
import DedekindZetaZeroFree.LFunctions.Hecke.PartialRayZetaRegularization
import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts
import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalUnitCharacter
import DedekindZetaZeroFree.LFunctions.Dedekind.FiniteEulerRestoration
import DedekindZetaZeroFree.HeckeCorollary

/-! A single entire counting function for a finite-order ray-class character
of any number field, including the characters with a pole at one. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set
open DedekindZetaZeroFree DedekindZetaZeroFree.AbelianQuotient
open scoped NumberField BigOperators Topology

noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable {m : Ideal (𝓞 K)} (hm : m ≠ ⊥) (χ : RayClassCharacter K m)

include hm in
private theorem rayHecke_series_ne_zero {w : ℂ} (hw : 1 < w.re) :
    (∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-w)) ≠ 0 := by
  have hcoef := ExteriorIdealEuler.zeroMaskedRay_isCoefficient
    (cS := (⊤ : Ideal (𝓞 K))) m hm χ ⊤
  have hprod := (ExteriorIdealEuler.exterior_ideal_euler _ hcoef w hw).2.2.1
  have hsupp : Function.support (fun I : Ideal (𝓞 K) =>
      χ I * (Ideal.absNorm I : ℂ) ^ (-w)) ⊆
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
    intro I hI
    refine ⟨?_, by simp⟩
    intro hzero
    exact hI (by simp [(χ.eq_zero_iff' I).mpr (Or.inl hzero)])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  change (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 K)),
    χ I.val * (Ideal.absNorm I.val : ℂ) ^ (-w)) ≠ 0
  simpa only [ExteriorIdealEuler.summand, ExteriorIdealEuler.zeroMaskedRayCoefficient,
    sup_top_eq, ite_true] using hprod

include hm in
private theorem exists_rayHeckeCountingFunction :
    ∃ F : NonzeroEntireFunction, ∀ w : ℂ, 1 < w.re →
      F w = (w - 1) * (∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-w)) := by
  classical
  obtain ⟨ψ, hψ, _⟩ := rayCharacterDescent K m hm χ
  obtain ⟨ρ, A, hA, hPartial⟩ := partialRayZetaRegularization K m hm
  let _ : Fintype (RayIdealClass K m hm) := Fintype.ofFinite _
  let G (w : ℂ) := ∑ c : RayIdealClass K m hm, ψ c * A c w
  let R (w : ℂ) := (w - 1) * G w + (∑ c : RayIdealClass K m hm, ψ c) * ρ
  have hG : Differentiable ℂ G := by
    convert Differentiable.sum (u := Finset.univ)
      (A := fun c : RayIdealClass K m hm ↦ fun w : ℂ ↦ ψ c * A c w)
      (fun c _ ↦ (hA c).const_mul (ψ c)) using 1
    ext w
    simp only [G, Finset.sum_apply]
  have hR : Differentiable ℂ R :=
    ((differentiable_id.sub (differentiable_const 1)).mul hG).add
      (differentiable_const _)
  have hMatch (w : ℂ) (hw : 1 < w.re) :
      R w = (w - 1) * (∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-w)) := by
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hw
      exact (lt_irrefl _ hw)
    have hTerm (I : Ideal (𝓞 K)) :
        (∑ c : RayIdealClass K m hm, ψ c *
          (if rayIdealClass K m hm I = some c then (Ideal.absNorm I : ℂ) ^ (-w) else 0)) =
        χ I * (Ideal.absNorm I : ℂ) ^ (-w) := by
      rw [hψ I]
      cases rayIdealClass K m hm I <;> simp
    have hSum :
        HasSum (fun I : Ideal (𝓞 K) ↦ ∑ c : RayIdealClass K m hm, ψ c *
          (if rayIdealClass K m hm I = some c then (Ideal.absNorm I : ℂ) ^ (-w) else 0))
          (∑ c : RayIdealClass K m hm, ψ c * (A c w + ρ / (w - 1))) :=
      hasSum_sum (s := Finset.univ) (fun c _ ↦ (hPartial c w hw).mul_left (ψ c))
    simp_rw [hTerm] at hSum
    rw [hSum.tsum_eq]
    simp only [R, G, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    field_simp [sub_ne_zero.mpr hw1]
  refine ⟨⟨R, hR, ⟨2, ?_⟩⟩, hMatch⟩
  rw [hMatch 2 (by norm_num)]
  exact mul_ne_zero (by norm_num) (rayHecke_series_ne_zero hm χ (by norm_num))

/-- The entire continuation of \((w-1)L(w,\chi)\) determined by the actual
ideal series. The extra factor is nonzero in the open critical strip. -/
def rayHeckeCountingFunction : NonzeroEntireFunction :=
  Classical.choose (exists_rayHeckeCountingFunction hm χ)

theorem rayHeckeCountingFunction_eq_series {w : ℂ} (hw : 1 < w.re) :
    rayHeckeCountingFunction hm χ w =
      (w - 1) * (∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-w)) :=
  Classical.choose_spec (exists_rayHeckeCountingFunction hm χ) w hw

/-- The same uncompleted Hecke series continued off its possible pole. -/
def rayHeckeContinuation (w : ℂ) : ℂ :=
  rayHeckeCountingFunction hm χ w / (w - 1)

theorem rayHeckeContinuation_differentiableOn :
    DifferentiableOn ℂ (rayHeckeContinuation hm χ) ({1}ᶜ : Set ℂ) :=
  (rayHeckeCountingFunction hm χ).differentiable.differentiableOn.div
    (differentiable_id.sub (differentiable_const 1)).differentiableOn
    (fun _ hw ↦ sub_ne_zero.mpr hw)

theorem rayHeckeContinuation_eq_series {w : ℂ} (hw : 1 < w.re) :
    rayHeckeContinuation hm χ w =
      ∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-w) := by
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw
    exact (lt_irrefl _ hw)
  rw [rayHeckeContinuation, rayHeckeCountingFunction_eq_series hm χ hw,
    mul_comm, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hw1)]

theorem rayHeckeContinuation_eqOn_of_right_match {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F ({1}ᶜ : Set ℂ))
    (hMatch : ∀ w : ℂ, 1 < w.re → rayHeckeContinuation hm χ w = F w) :
    Set.EqOn (rayHeckeContinuation hm χ) F ({1}ᶜ : Set ℂ) := by
  have hConn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    ((rayHeckeContinuation_differentiableOn hm χ).analyticOnNhd isOpen_compl_singleton)
    (hF.analyticOnNhd isOpen_compl_singleton) hConn (z₀ := 2) (by simp) ?_
  exact Filter.eventually_of_mem
    ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by simp : 1 < (2 : ℂ).re)) hMatch

theorem rayHeckeContinuation_ne_zero_of_right_edge {w : ℂ}
    (hw : 31 / 32 < w.re) (hw₁ : w ≠ 1) :
    rayHeckeContinuation hm χ w ≠ 0 := by
  obtain ⟨F, hF, _, hSeries, hNonzero⟩ :=
    DedekindZetaZeroFree.heckeL_ne_zero K m hm χ
  have hEq := rayHeckeContinuation_eqOn_of_right_match hm χ hF (fun z hz ↦
    (rayHeckeContinuation_eq_series hm χ hz).trans (hSeries z hz).tsum_eq)
  rw [hEq hw₁]
  exact hNonzero w hw (Or.inl hw₁)

theorem rayHeckeCountingFunction_zero_iff {w : ℂ} (hw : w ≠ 1) :
    rayHeckeCountingFunction hm χ w = 0 ↔ rayHeckeContinuation hm χ w = 0 := by
  simp only [rayHeckeContinuation, div_eq_zero_iff, sub_ne_zero.mpr hw, or_false]

theorem rayHeckeCountingFunction_order_eq {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt (rayHeckeCountingFunction hm χ).toFun w =
      analyticOrderNatAt (rayHeckeContinuation hm χ) w := by
  have hL := (rayHeckeContinuation_differentiableOn hm χ).analyticOnNhd
    isOpen_compl_singleton w hw
  have hFactor : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) w :=
    (differentiable_id.sub (differentiable_const 1)).analyticAt w
  have heq : (rayHeckeCountingFunction hm χ).toFun =ᶠ[𝓝 w]
      ((fun z : ℂ ↦ z - 1) * rayHeckeContinuation hm χ) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
    change rayHeckeCountingFunction hm χ z = (z - 1) * rayHeckeContinuation hm χ z
    rw [rayHeckeContinuation, mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr hz)]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hFactor hL,
    hFactor.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hw), zero_add]

theorem rayHeckeRH_iff_cofinal_counts :
    StripZerosOnLine (rayHeckeContinuation hm χ) ↔
      ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
        (rayHeckeCountingFunction hm χ).stripZeroCount T (fun _ ↦ True) =
          (rayHeckeCountingFunction hm χ).stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  rw [← (rayHeckeCountingFunction hm χ).stripZerosOnLine_iff_cofinalCounts]
  constructor <;> intro h w hlo hhi hz
  · have hw : w ≠ 1 := fun he ↦ by rw [he, Complex.one_re] at hhi; exact (lt_irrefl _ hhi)
    exact h w hlo hhi ((rayHeckeCountingFunction_zero_iff hm χ hw).mp hz)
  · have hw : w ≠ 1 := fun he ↦ by rw [he, Complex.one_re] at hhi; exact (lt_irrefl _ hhi)
    exact h w hlo hhi ((rayHeckeCountingFunction_zero_iff hm χ hw).mpr hz)

theorem unitRayHecke_isDedekind (K : Type) [Field K] [NumberField K] :
    IsDedekindZeta K
      (rayHeckeContinuation top_ne_bot (LargeSieve.principalUnitRayCharacter K)) := by
  refine ⟨rayHeckeContinuation_differentiableOn _ _, fun w hw ↦ ?_⟩
  rw [rayHeckeContinuation_eq_series _ _ hw]
  exact PrincipalPointwise.principal_top_series_eq_dedekindZeta K _
    (LargeSieve.principalUnitRayCharacter_isPrincipal K) w hw

theorem dedekindZetaRH_iff_unit_rayHecke (K : Type) [Field K] [NumberField K] :
    DedekindZetaRH K ↔
      StripZerosOnLine
        (rayHeckeContinuation top_ne_bot (LargeSieve.principalUnitRayCharacter K)) :=
  dedekindZetaRH_iff_strip (unitRayHecke_isDedekind K)

#check @rayHeckeRH_iff_cofinal_counts
#check @dedekindZetaRH_iff_unit_rayHecke
#print axioms rayHeckeCountingFunction_eq_series
#print axioms rayHeckeContinuation_eq_series
#print axioms rayHeckeCountingFunction_order_eq
#print axioms rayHeckeRH_iff_cofinal_counts
#print axioms rayHeckeContinuation_ne_zero_of_right_edge
#print axioms dedekindZetaRH_iff_unit_rayHecke

end
end FieldTarget
