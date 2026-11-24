import DottieProductionBounds
import DottieShorterOmittedBudget

/-! A sharper budget at the archived height from the already checked score. -/
namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open private phase_projection_error from DottieRationalProjection
set_option autoImplicit false

private theorem reference_scale_tight :
    2 / (203 * 10^26) ≤
      (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale) *
        ‖(archivedThetaScale : ℂ)^dottieReferencePoint‖ := by
  let B := archivedThetaScale
  let T := dottieHeight
  let z := dottieReferencePoint
  let G := ‖Gamma (2 + (T : ℂ)*I)‖
  have hB : 0 < B := archivedThetaScale_pos
  have hT : 0 < T := by dsimp only [T]; linarith only [dottieHeight_enclosure.1]
  have hT' : T ≤ 453 * 10^10 := by dsimp only [T]; linarith only [dottieHeight_enclosure.2]
  have hB' : B ≤ 1640000 := by
    have hs : √(26509772707289 : ℝ) ≤ 5149600 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hp : (3.14 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d20]
    change Real.sqrt 26509772707289 / Real.pi ≤ 1640000
    exact (div_le_iff₀ Real.pi_pos).2 (by linarith only [hs, hp])
  have hBroot : √B ≤ 1281 := Real.sqrt_le_iff.mpr ⟨by norm_num, hB'.trans (by norm_num)⟩
  have hTroot : √T ≤ 2129000 := Real.sqrt_le_iff.mpr ⟨by norm_num, hT'.trans (by norm_num)⟩
  have hproduct : B * √B * T * √T ≤ 203 * 10^26 := calc
    _ ≤ (1640000 : ℝ) * 1281 * (453 * 10^10) * 2129000 := by gcongr
    _ ≤ _ := by norm_num
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hBroot₀ := Real.sqrt_pos_of_pos hB
  have hratio : (T * √T)⁻¹ ≤ ‖Gamma z‖ / G := by
    have he : T ^ (-(3/2 : ℝ)) = (T * √T)⁻¹ := by
      rw [Real.rpow_neg hT.le, show (3/2 : ℝ) = 1 + 1/2 by norm_num,
        Real.rpow_add hT, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [← he]
    exact dottie_reference_gamma_norm_ratio_lower
  have hz : z.re = 1/2 := by norm_num [z, dottieReferencePoint, Complex.mul_re]
  have hbpow : ‖(B : ℂ)^z‖ = √B := by
    rw [norm_cpow_eq_rpow_re_of_pos hB, hz, ← Real.sqrt_eq_rpow]
  change 2 / (203 * 10^26) ≤ (2 * ‖Gamma z‖ / (B^2*G)) * ‖(B : ℂ)^z‖
  rw [hbpow, show 2 * ‖Gamma z‖ / (B^2*G) * √B =
      (2 / (B*√B)) * (‖Gamma z‖/G) by
    field_simp [hB.ne', hG.ne', hBroot₀.ne']
    rw [Real.sq_sqrt hB.le]]
  calc
    _ ≤ 2 / (B*√B*T*√T) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hproduct
    _ = (2 / (B*√B)) * (T*√T)⁻¹ := by
      field_simp [hB.ne', hBroot₀.ne', hT.ne', (Real.sqrt_pos_of_pos hT).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

/-- The exact checked integer score implies a larger reference allowance. -/
theorem dottieProductionCircleReference_tight : (15 : ℝ) / (2 * 10^30) ≤ dottieCircleReference := by
  have hscore : (1716 / 10000 : ℝ) ≤ (dottieQuickReferenceScore : ℝ) / (fixedCosScale : ℝ)^5 := by
    rw [dottieQuickReferenceScore_eq_row_span, dottieProductionFullSpan_eq_candidate]
    norm_num [dottiePairedCandidateTicks, fixedCosScale]
  have hp : (1316 / 10000 : ℝ) ≤ dottieRationalReferenceProjection := by
    have he := (abs_le.mp dottie_quick_reference_score_error).2
    linarith only [he, hscore]
  obtain ⟨φ, hφ₁, hφ₂, href⟩ := dottieCircleReference_eq_completed_phase
  have hφ : |φ - 3.9229252| ≤ 0.00000151 := by
    exact abs_le.mpr ⟨by linarith only [hφ₁], by linarith only [hφ₂]⟩
  have hm := mul_le_mul hφ dottie_reference_rational_norm_bound (norm_nonneg _) (by norm_num)
  have he := phase_projection_error
    (signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint)
    (signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieRationalReferencePoint)
    φ 3.9229252
  rw [show ((↑(3.9229252 : ℝ)) : ℂ) = 3.9229252 by norm_num] at he
  change |(Complex.exp ((φ : ℂ)*I) * _).re - dottieRationalReferenceProjection| ≤ _ at he
  have hproj : (381 / 5000 : ℝ) ≤
      |(Complex.exp ((φ : ℂ)*I) *
        signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re| := by
    have hmove : -(1/200 + 0.00000151*33276 : ℝ) ≤
        (Complex.exp ((φ : ℂ)*I) *
          signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re -
            dottieRationalReferenceProjection := by
      exact (neg_le_neg (he.trans (by linarith only [hm, dottie_reference_rational_height_error]))).trans
        (neg_abs_le _)
    refine le_trans ?_ (le_abs_self _)
    linarith only [hp, hmove]
  rw [href]
  calc
    _ ≤ (2 / (203 * 10^26) : ℝ) * (381 / 5000) := by norm_num
    _ ≤ _ := mul_le_mul reference_scale_tight hproj (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 2 / (203 * 10^26)).trans reference_scale_tight)

/-- The `8 * 10^24` far part consumes at most 0.11 of the original signed unit. -/
theorem dottieProductionEarlierFar_tight_budget {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieEarlierFarSmooth w‖ ≤ (11/100) * ((w.re-1/2) * dottieCircleReference) := by
  obtain ⟨hr, hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hf : ‖dottieEarlierFarSmooth w‖ ≤ 2/(5*10^33) :=
    dottie_smooth_subset_uniform_absolute _ (fun _ hn => (Finset.mem_filter.mp hn).2) hr hi
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hprod := mul_le_mul hx dottieProductionCircleReference_tight (by norm_num) (by linarith only [hx])
  exact hf.trans (by nlinarith only [hprod])

theorem dottieProductionLowerSmooth_tight_budget {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieOmittedLowerSmoothingError w‖ ≤ (1/200000) * ((w.re-1/2) * dottieCircleReference) := by
  obtain ⟨hr, hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hprod := mul_le_mul hx dottieProductionCircleReference_tight (by norm_num) (by linarith only [hx])
  exact (dottie_lower_omitted_smoothing_uniform_absolute hr hi).trans (by nlinarith only [hprod])

/-- Keep the same omitted term and circle while widening the signed allowance. -/
theorem dottieProductionOmitted_of_tight_signed {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (hsigned : (dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w).im ≤
      (188889/1000) * ((w.re-1/2)*dottieCircleReference)) :
    (dottieOmitted w).im ≤ 189 * ((w.re-1/2)*dottieCircleReference) := by
  have hl := (le_abs_self (dottieOmittedLowerSmoothingError w).im).trans
    ((Complex.abs_im_le_norm _).trans (dottieProductionLowerSmooth_tight_budget hw))
  have hf := (le_abs_self (dottieEarlierFarSmooth w).im).trans
    ((Complex.abs_im_le_norm _).trans (dottieProductionEarlierFar_tight_budget hw))
  have hscale : 0 ≤ (w.re-1/2)*dottieCircleReference :=
    (by norm_num : (0 : ℝ) ≤ (1/2048)*(2/10^30)).trans (dottieProductionCircleScale_lower hw)
  have hsplit : dottieOmitted w = (dottieOmittedSharpBlock w+dottieShorterMiddleSmooth w) +
      dottieOmittedLowerSmoothingError w + dottieEarlierFarSmooth w := by
    rw [dottieOmitted_eq_sharp_add_middle_add_errors]
    calc
      _ = dottieOmittedSharpBlock w + (dottieOmittedMiddleSmooth w+dottieOmittedFarSmooth w) +
          dottieOmittedLowerSmoothingError w := by abel
      _ = _ := by rw [dottie_middle_add_far_eq_shorter_split]; abel
  rw [hsplit, Complex.add_im, Complex.add_im]
  linarith only [hsigned, hl, hf, hscale]

#print axioms dottieProductionCircleReference_tight
#print axioms dottieProductionEarlierFar_tight_budget
#print axioms dottieProductionLowerSmooth_tight_budget
#print axioms dottieProductionOmitted_of_tight_signed

end QuarticModel
