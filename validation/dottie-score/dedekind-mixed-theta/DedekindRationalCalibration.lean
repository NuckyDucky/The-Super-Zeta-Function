import DedekindMixedTheta
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace FieldTarget

open Complex Filter NumberField Set
open DedekindZetaZeroFree.AbelianQuotient
open scoped Topology

private theorem rat_absNorm_span_nat (n : ℕ) :
    (Ideal.span {(n : 𝓞 ℚ)}).absNorm = n := by
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem rat_ideal_eq_span_absNorm (J : Ideal (𝓞 ℚ)) :
    J = Ideal.span {(J.absNorm : 𝓞 ℚ)} := by
  let e := Rat.ringOfIntegersEquiv
  let _ : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let x := Submodule.IsPrincipal.generator J
  let n := (e x).natAbs
  have hassoc : Associated x (n : 𝓞 ℚ) := by
    have h := Associated.map e.symm (Int.associated_natAbs (e x))
    rwa [e.symm_apply_apply, map_natCast] at h
  have hspan : J = Ideal.span {(n : 𝓞 ℚ)} :=
    (Ideal.span_singleton_generator J).symm.trans
      (Ideal.span_singleton_eq_span_singleton.mpr hassoc)
  have hn : J.absNorm = n := by rw [hspan, rat_absNorm_span_nat]
  rwa [hn]

/-- The ideal coefficient at every natural norm over the rational field is one. -/
theorem rat_ideal_norm_card (n : ℕ) :
    Nat.card {J : Ideal (𝓞 ℚ) // J.absNorm = n} = 1 := by
  let _ : Nonempty {J : Ideal (𝓞 ℚ) // J.absNorm = n} :=
    ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, rat_absNorm_span_nat n⟩⟩
  let _ : Subsingleton {J : Ideal (𝓞 ℚ) // J.absNorm = n} := ⟨by
    intro J H
    apply Subtype.ext
    exact ((rat_ideal_eq_span_absNorm J.val).trans (by rw [J.property])).trans
      ((rat_ideal_eq_span_absNorm H.val).trans (by rw [H.property])).symm⟩
  exact Nat.card_unique

private theorem rat_dedekindZeta_eq_riemannZeta {w : ℂ} (hw : 1 < w.re) :
    NumberField.dedekindZeta ℚ w = riemannZeta w := by
  have h : (fun n ↦ (Nat.card {J : Ideal (𝓞 ℚ) // J.absNorm = n} : ℂ)) = 1 := by
    funext n
    simp [rat_ideal_norm_card]
  rw [NumberField.dedekindZeta, h]
  exact LSeries_one_eq_riemannZeta hw

private theorem rat_zetaGammaFactor (w : ℂ) : zetaGammaFactor ℚ w = Gammaℝ w := by
  have hr : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
  simp [zetaGammaFactor,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hr,
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hr]

private theorem rat_mixedTheta_completed {w : ℂ} (hw : 1 < w.re) :
    (Theta.mixedThetaPair ℚ).Λ w = completedRiemannZeta w := by
  let P := Theta.mixedThetaPair ℚ
  have hk : P.k = 1 := Theta.mixedThetaPair_k ℚ
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  calc
    P.Λ w = zetaGammaFactor ℚ w * NumberField.dedekindZeta ℚ w :=
      (P.hasMellin (s := w) (by rwa [hk])).2.symm.trans (Theta.hasMellin_mixedThetaPair ℚ hw).2
    _ = completedRiemannZeta w := by
      rw [rat_zetaGammaFactor, rat_dedekindZeta_eq_riemannZeta hw, riemannZeta_def_of_ne_zero hw0,
        mul_comm, div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hw))]

private theorem rightHalfPlane_mem_nhds_two : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

/-- The rational-field mixed theta regular part and pole coefficient are the classical ones. -/
theorem rat_mixedTheta_regular_part_and_constant :
    (Theta.mixedThetaPair ℚ).Λ₀ = completedRiemannZeta₀ ∧ (Theta.mixedThetaPair ℚ).f₀ = 1 := by
  let P := Theta.mixedThetaPair ℚ
  let D : ℂ → ℂ := fun w ↦ w * (1 - w) * (P.Λ₀ w - completedRiemannZeta₀ w)
  have hD : Differentiable ℂ D :=
    (differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)).mul
      (P.differentiable_Λ₀.sub differentiable_completedZeta₀)
  have hlocal : ∀ w : ℂ, 1 < w.re → D w = P.f₀ - 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
    have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw
    have hk : P.k = 1 := Theta.mixedThetaPair_k ℚ
    have hg : P.g₀ = P.f₀ := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ ℚ
    have he : P.ε = 1 := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_ε_eq_one ℚ
    have hc : w * (1 - w) * P.Λ w = w * (1 - w) * P.Λ₀ w - P.f₀ := by
      calc
        _ = -DedekindZetaZeroFree.Hecke.poleCleared P w := by
          rw [DedekindZetaZeroFree.Hecke.poleCleared_eq P hk w hw0 hw1]
          ring
        _ = _ := by rw [DedekindZetaZeroFree.Hecke.poleCleared, hg, he]; ring
    rw [rat_mixedTheta_completed hw, completedRiemannZeta_eq] at hc
    have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr hw1.symm
    dsimp [D]
    field_simp [hw0, h1w] at hc
    linear_combination -hc
  have hDeq : D = fun _ ↦ P.f₀ - 1 :=
    (hD.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      ((differentiable_const (P.f₀ - 1)).differentiableOn.analyticOnNhd isOpen_univ) (by
      filter_upwards [rightHalfPlane_mem_nhds_two] with w hw using hlocal w hw)
  have hf : P.f₀ = 1 := by
    have hz := congrFun hDeq 1
    have hz' : 0 = P.f₀ - 1 := by simpa [D] using hz
    exact sub_eq_zero.mp hz'.symm
  refine ⟨(P.differentiable_Λ₀.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := 2) ?_, hf⟩
  filter_upwards [rightHalfPlane_mem_nhds_two] with w hw
  have hw' : 1 < w.re := hw
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw'
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw'
  have hz : D w = 0 := by rw [hlocal w hw', hf, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero hw0 (sub_ne_zero.mpr hw1.symm)))

#check @rat_mixedTheta_regular_part_and_constant
#print axioms rat_ideal_norm_card
#print axioms rat_mixedTheta_regular_part_and_constant

end FieldTarget
