import DottieReferenceCandidate
import DottieReferenceGammaLower
import DottieFarNumeric

/-! A quantitative reference lower bound from the same exact integer
comparison used by the archived positivity proof. -/

namespace QuarticModel

open Complex
open SuperZeta.StirlingCorrection
open private phase_projection_error from DottieRationalProjection
open private rational_projection_gt_of_score from DottieReferenceScore
set_option autoImplicit false
private theorem projection_lower (D D₀ : ℂ) (φ : ℝ)
    (hφ₁ : 3.92292369 < φ) (hφ₂ : φ < 3.92292670)
    (hD : ‖D-D₀‖ < 1/200) (hD₀ : ‖D₀‖ ≤ 33276)
    (hproj : 1/10 < (Complex.exp ((3.9229252 : ℂ)*I)*D₀).re) :
    1/25 ≤ |(Complex.exp ((φ : ℂ)*I)*D).re| := by
  have hφ : |φ-3.9229252| ≤ 0.0000016 :=
    abs_le.mpr ⟨by linarith only [hφ₁], by linarith only [hφ₂]⟩
  have he := phase_projection_error D D₀ φ 3.9229252
  have hp := mul_le_mul hφ hD₀ (norm_nonneg _) (by norm_num)
  have hmove : |(Complex.exp ((φ : ℂ)*I)*D).re-
      (Complex.exp ((3.9229252 : ℂ)*I)*D₀).re| < 3/50 := by
    rw [show ((↑(3.9229252 : ℝ)) : ℂ) = 3.9229252 by norm_num] at he
    linarith only [he,hp,hD]
  have hr := (abs_lt.mp hmove).1
  exact (show (1/25 : ℝ) ≤ (Complex.exp ((φ : ℂ)*I)*D).re by
    linarith only [hr,hproj]).trans (le_abs_self _)

private theorem reference_scalar_lower {B T G N : ℝ}
    (hB : 0 < B) (hB' : B ≤ 2*10^6) (hT : 0 < T) (hT' : T ≤ 5*10^12)
    (hG : 0 < G) (hγ : T^(-(3/2 : ℝ)) ≤ N/G) :
    2/(4*10^28) ≤ 2*N/(B^2*G)*√B := by
  have hBroot : √B ≤ 1500 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, hB'.trans (by norm_num)⟩
  have hTroot : √T ≤ 2500000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, hT'.trans (by norm_num)⟩
  have hprod : B*√B*T*√T ≤ 4*10^28 := calc
    _ ≤ (2*10^6 : ℝ)*1500*(5*10^12)*2500000 := by gcongr
    _ ≤ _ := by norm_num
  have hrootB : 0 < √B := Real.sqrt_pos_of_pos hB
  have hrootT : 0 < √T := Real.sqrt_pos_of_pos hT
  have hratio : (T*√T)⁻¹ ≤ N/G := by
    have hpow : T^(-(3/2 : ℝ)) = (T*√T)⁻¹ := by
      rw [Real.rpow_neg hT.le, show (3/2 : ℝ) = 1+1/2 by norm_num,
        Real.rpow_add hT, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [← hpow]
    exact hγ
  have hcoef : 2*N/(B^2*G)*√B = (2/(B*√B))*(N/G) := by
    field_simp [hB.ne', hG.ne', hrootB.ne']
    rw [Real.sq_sqrt hB.le]
  rw [hcoef]
  have hc : 2/(4*10^28 : ℝ) ≤ 2/(B*√B*T*√T) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod
  refine hc.trans ?_
  have heq : 2/(B*√B*T*√T) = (2/(B*√B))*(T*√T)⁻¹ := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hratio (by positivity)

private theorem lower_of_phase_bounds {S C : ℝ} {D D₀ : ℂ}
    (hphase : ∃ φ : ℝ, 3.92292369 < φ ∧ φ < 3.92292670 ∧
      S = C * |(Complex.exp ((φ : ℂ)*I)*D).re|)
    (hC : 2/(4*10^28) ≤ C) (hD : ‖D-D₀‖ < 1/200) (hD₀ : ‖D₀‖ ≤ 33276)
    (hproj : 1/10 < (Complex.exp ((3.9229252 : ℂ)*I)*D₀).re) :
    2/10^30 ≤ S := by
  obtain ⟨φ,hφ₁,hφ₂,hRef⟩ := hphase
  have habs := projection_lower D D₀ φ hφ₁ hφ₂ hD hD₀ hproj
  rw [hRef]
  calc
    _ = (2/(4*10^28 : ℝ))*(1/25) := by norm_num
    _ ≤ _ := mul_le_mul hC habs (by norm_num) ((by norm_num : (0 : ℝ) ≤ 2/(4*10^28)).trans hC)

private theorem dottie_reference_prefactor_lower :
    2/(4*10^28) ≤
      (2*‖Gamma dottieReferencePoint‖/archivedDottieCompletionScale) *
        ‖(archivedThetaScale : ℂ)^dottieReferencePoint‖ := by
  let B := archivedThetaScale
  let T := dottieHeight
  let z := dottieReferencePoint
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  have hT : 0 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hT' : T ≤ 5*10^12 := by dsimp [T]; linarith only [dottieHeight_enclosure.2]
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hz : z.re = 1/2 := by norm_num [z, dottieReferencePoint, Complex.mul_re]
  have hB := archivedThetaScale_pos
  have hpow : ‖(B : ℂ)^z‖ = √B := by
    rw [norm_cpow_eq_rpow_re_of_pos hB, hz, ← Real.sqrt_eq_rpow]
  change 2/(4*10^28) ≤ 2*‖Gamma z‖/(B^2*G)*‖(B : ℂ)^z‖
  rw [hpow]
  exact reference_scalar_lower hB dottie_theta_scale_lt_two_million.le hT hT' hG
    dottie_reference_gamma_norm_ratio_lower

theorem dottieCircleReference_lower_of_quick_score
    (h : 7*(fixedCosScale : ℤ)^5 < 50*dottieQuickReferenceScore) :
    2/10^30 ≤ dottieCircleReference := by
  exact lower_of_phase_bounds dottieCircleReference_eq_completed_phase dottie_reference_prefactor_lower
    dottie_reference_rational_height_error dottie_reference_rational_norm_bound
    (rational_projection_gt_of_score dottie_quick_reference_score_error h)

theorem dottieCircleReference_lower_of_candidate_equality
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 =
      dottiePairedCandidateTicks) : 2/10^30 ≤ dottieCircleReference := by
  apply dottieCircleReference_lower_of_quick_score
  rw [dottieQuickReferenceScore_eq_row_span, hscore]
  exact dottie_paired_candidate_clears_reference_threshold

theorem dottie_far_budget_of_reference_lower
    (hS : 2/10^30 ≤ dottieCircleReference) {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieOmittedFarSmooth w‖ ≤ (465/1000)*((w.re-1/2)*dottieCircleReference) := by
  have hdist : ‖w-archivedRightCenter dottieHeight‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w-archivedRightCenter dottieHeight)
  have him := Complex.abs_im_le_norm (w-archivedRightCenter dottieHeight)
  rw [hdist, sub_re] at hre
  rw [hdist, sub_im] at him
  norm_num [archivedRightCenter] at hre him
  have hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048) :=
    ⟨by linarith only [(abs_le.mp hre).1], by linarith only [(abs_le.mp hre).2]⟩
  have hi : |w.im-dottieHeight| ≤ 35/2048 :=
    abs_le.mpr ⟨by linarith only [(abs_le.mp him).1], by linarith only [(abs_le.mp him).2]⟩
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  refine (dottie_far_omitted_uniform_absolute hr hi).trans ?_
  have hh := mul_le_mul hx hS (by norm_num) (by linarith only [hx])
  nlinarith only [hh]

theorem dottie_far_budget_of_candidate_equality
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 =
      dottiePairedCandidateTicks) {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieOmittedFarSmooth w‖ ≤ (465/1000)*((w.re-1/2)*dottieCircleReference) :=
  dottie_far_budget_of_reference_lower (dottieCircleReference_lower_of_candidate_equality hscore) hw

#print axioms dottieCircleReference_lower_of_quick_score
#print axioms dottieCircleReference_lower_of_candidate_equality
#print axioms dottie_far_budget_of_reference_lower
#print axioms dottie_far_budget_of_candidate_equality

end QuarticModel
