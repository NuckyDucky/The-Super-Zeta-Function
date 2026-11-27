import DedekindMixedThetaRegularPartBound
import DedekindRationalCalibration

namespace FieldTarget

set_option autoImplicit false

open Complex Filter NumberField Set
open DedekindZetaZeroFree.AbelianQuotient
open DedekindZetaZeroFree.Hecke (poleCleared poleCleared_eq mixedThetaPair_global_g₀_eq_f₀
  mixedThetaPair_global_ε_eq_one)
open private rat_mixedTheta_completed from DedekindRationalCalibration
open scoped Topology

/-- Clearing both poles gives the mixed theta constant at one and the
regularized Mellin value as its derivative there. -/
theorem mixedTheta_poleCleared_value_and_slope (K : Type) [Field K] [NumberField K] :
    poleCleared (Theta.mixedThetaPair K) 1 = (Theta.mixedThetaPair K).f₀ ∧
      HasDerivAt (poleCleared (Theta.mixedThetaPair K)) ((Theta.mixedThetaPair K).Λ₀ 1) 1 := by
  let P := Theta.mixedThetaPair K
  have heq : poleCleared P = fun w : ℂ ↦ w * (w - 1) * P.Λ₀ w + P.f₀ := by
    funext w
    rw [poleCleared, mixedThetaPair_global_g₀_eq_f₀ K, mixedThetaPair_global_ε_eq_one K]
    ring
  change poleCleared P 1 = P.f₀ ∧ HasDerivAt (poleCleared P) (P.Λ₀ 1) 1
  rw [heq]
  refine ⟨by simp, ?_⟩
  have hI := hasDerivAt_id (1 : ℂ)
  have hpoly : HasDerivAt (fun w : ℂ ↦ w * (w - 1)) 1 1 := by
    simpa using hI.fun_mul (hI.sub_const 1)
  simpa using (hpoly.fun_mul (P.differentiable_Λ₀ 1).hasDerivAt).add_const P.f₀

/-- Factor the Dedekind series as ordinary zeta times `B` on its convergence
domain. If the remaining factor with its completion ratio extends holomorphically
to the right half-plane, the field's regularized value only uses that factor's
value and derivative at one. -/
theorem mixedTheta_regular_part_of_dedekind_factor (K : Type) [Field K] [NumberField K]
    {B : ℂ → ℂ} (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re})
    (hfactor : ∀ w : ℂ, 1 < w.re →
      NumberField.dedekindZeta K w = riemannZeta w * B w)
    (hweight : ∀ w : ℂ, 1 < w.re → F w = zetaGammaFactor K w / Gammaℝ w * B w) :
    (Theta.mixedThetaPair K).f₀ = F 1 ∧
      (Theta.mixedThetaPair K).Λ₀ 1 = F 1 * completedRiemannZeta₀ 1 + deriv F 1 := by
  let P := Theta.mixedThetaPair K
  let Q := Theta.mixedThetaPair ℚ
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconnected : IsPreconnected U := (convex_halfSpace_gt Complex.reCLM.isLinear 0).isPreconnected
  have hK : Differentiable ℂ (poleCleared P) :=
    DedekindZetaZeroFree.Hecke.poleCleared_differentiable P (Theta.mixedThetaPair_k K)
  have hQ : Differentiable ℂ (poleCleared Q) :=
    DedekindZetaZeroFree.Hecke.poleCleared_differentiable Q (Theta.mixedThetaPair_k ℚ)
  have htwo : (2 : ℂ) ∈ U := by change (0 : ℝ) < (2 : ℂ).re; norm_num
  have hrgt : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have heq₂ : poleCleared P =ᶠ[𝓝 (2 : ℂ)] fun w ↦ F w * poleCleared Q w := by
    filter_upwards [hrgt] with w hw
    have hr : 1 < w.re := hw
    have hw0 : w ≠ 0 := by rintro rfl; norm_num at hr
    have hw1 : w ≠ 1 := by rintro rfl; norm_num at hr
    have hk : P.k = 1 := Theta.mixedThetaPair_k K
    have hΛ : P.Λ w = zetaGammaFactor K w * NumberField.dedekindZeta K w :=
      (P.hasMellin (s := w) (by rwa [hk])).2.symm.trans (Theta.hasMellin_mixedThetaPair K hr).2
    have hΛQ : Q.Λ w = completedRiemannZeta w := rat_mixedTheta_completed hr
    change poleCleared P w = F w * poleCleared Q w
    rw [poleCleared_eq P hk w hw0 hw1, poleCleared_eq Q (Theta.mixedThetaPair_k ℚ) w hw0 hw1,
      hΛ, hΛQ, hfactor w hr, hweight w hr, riemannZeta_def_of_ne_zero hw0]
    ring
  have heq := (hK.differentiableOn.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    ((hF.mul hQ.differentiableOn).analyticOnNhd hU) hconnected htwo heq₂
  have hone : (1 : ℂ) ∈ U := by change (0 : ℝ) < (1 : ℂ).re; norm_num
  have hnear : poleCleared P =ᶠ[𝓝 (1 : ℂ)] fun w ↦ F w * poleCleared Q w := by
    filter_upwards [hU.mem_nhds hone] with w hw using heq hw
  obtain ⟨hKval, hKderiv⟩ := mixedTheta_poleCleared_value_and_slope K
  obtain ⟨hQval, hQderiv⟩ := mixedTheta_poleCleared_value_and_slope ℚ
  rw [rat_mixedTheta_regular_part_and_constant.1] at hQderiv
  rw [rat_mixedTheta_regular_part_and_constant.2] at hQval
  have hAt : DifferentiableAt ℂ F 1 := hF.differentiableAt (hU.mem_nhds hone)
  have hprod : HasDerivAt (fun w ↦ F w * poleCleared Q w)
      (F 1 * completedRiemannZeta₀ 1 + deriv F 1) 1 := by
    simpa [hQval, add_comm] using hAt.hasDerivAt.fun_mul hQderiv
  refine ⟨?_, hKderiv.deriv.symm.trans (hnear.hasDerivAt_iff.mpr hprod).deriv⟩
  have hv := hnear.eq_of_nhds
  change poleCleared P 1 = F 1 * poleCleared Q 1 at hv
  change P.f₀ = F 1
  rw [← hKval, hv, hQval, mul_one]

theorem finite_dottie_boundary_of_dedekind_factor_slope (K : Type) [Field K] [NumberField K]
    {B : ℂ → ℂ} (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re})
    (hfactor : ∀ w : ℂ, 1 < w.re → NumberField.dedekindZeta K w = riemannZeta w * B w)
    (hweight : ∀ w : ℂ, 1 < w.re → F w = zetaGammaFactor K w / Gammaℝ w * B w)
    {L : ℝ} (hL : 0 ≤ L)
    (hslope : 2 * (F 1 * completedRiemannZeta₀ 1 + deriv F 1).re <
      ‖F 1‖ / (1 + (L + 31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K)
      (-L) L := by
  obtain ⟨hconst, hpart⟩ := mixedTheta_regular_part_of_dedekind_factor K F hF hfactor hweight
  apply finite_dottie_boundary_of_regularized_one K hL
  simpa only [hconst, hpart] using hslope

#check @mixedTheta_poleCleared_value_and_slope
#check @mixedTheta_regular_part_of_dedekind_factor
#check @finite_dottie_boundary_of_dedekind_factor_slope
#print axioms mixedTheta_poleCleared_value_and_slope
#print axioms mixedTheta_regular_part_of_dedekind_factor
#print axioms finite_dottie_boundary_of_dedekind_factor_slope

end FieldTarget
