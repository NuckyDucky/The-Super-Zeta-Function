import DottieOmittedSharpVariation
import ArchivedDottieRangeIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Reflection makes the omitted imaginary contribution a horizontal
difference. A one-sided derivative bound supplies the circle's signed
budget with its exact factor of the horizontal displacement. -/

namespace QuarticModel

open Complex Finset Set
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection

private def dottieMiddleNorms : Finset ℕ :=
  dottieOmittedNorms.filter (fun n => dottieOmittedSharpEnd < n ∧ n ≤ dottieOmittedFarCut)

noncomputable def dottieJointOmittedSide (w : ℂ) : ℂ :=
  dottieSharpFactor w * dottieNormBlock dottiePrefixEnd (dottieOmittedSharpEnd-dottiePrefixEnd) w +
    dottieRangeSide dottieMiddleNorms w

theorem dottie_joint_omitted_eq_two_sides {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w =
      dottieJointOmittedSide w + conj (dottieJointOmittedSide (1-conj w)) := by
  have hS : ∀ n ∈ dottieMiddleNorms, n ≠ 0 := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2.1
    omega
  have hwr : 0 < (1-conj w).re+1 := by
    simp only [sub_re, one_re, conj_re]
    linarith
  have hm : dottieOmittedMiddleSmooth w = dottieRangeSide dottieMiddleNorms w +
      conj (dottieRangeSide dottieMiddleNorms (1-conj w)) := by
    rw [dottie_range_side_eq_sum dottieMiddleNorms (by linarith : 0 < w.re+1) hS,
      dottie_range_side_eq_sum dottieMiddleNorms hwr hS, map_sum, ← Finset.sum_add_distrib]
    rfl
  rw [dottie_omitted_sharp_eq_norm_block, hm, dottieJointOmittedSide, dottieJointOmittedSide,
    map_add]
  ring

noncomputable def dottieOmittedHorizontal (t r : ℝ) : ℝ :=
  (dottieJointOmittedSide ⟨r,t⟩).im

theorem dottie_joint_omitted_im_le_of_horizontal_slope {w : ℂ}
    (hw₀ : 1/2 ≤ w.re) (hw₁ : w.re < 1) (M : ℝ)
    (hcont : ContinuousOn (dottieOmittedHorizontal w.im) (Icc (1-w.re) w.re))
    (hdiff : DifferentiableOn ℝ (dottieOmittedHorizontal w.im) (Ioo (1-w.re) w.re))
    (hslope : ∀ r ∈ Ioo (1-w.re) w.re, deriv (dottieOmittedHorizontal w.im) r ≤ M) :
    (dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w).im ≤ 2 * M * (w.re-1/2) := by
  have hx : 1-w.re ≤ w.re := by linarith
  have hb := (convex_Icc (1-w.re) w.re).image_sub_le_mul_sub_of_deriv_le hcont
    (by rwa [interior_Icc]) (by rwa [interior_Icc])
    (1-w.re) ⟨le_rfl,hx⟩ w.re ⟨hx,le_rfl⟩ hx
  have hr : (⟨1-w.re,w.im⟩ : ℂ) = 1-conj w := by
    apply Complex.ext <;> simp
  unfold dottieOmittedHorizontal at hb
  rw [hr] at hb
  change ((dottieJointOmittedSide w).im - (dottieJointOmittedSide (1-conj w)).im ≤ _) at hb
  rw [dottie_joint_omitted_eq_two_sides (by linarith : 0 < w.re) hw₁, add_im, conj_im]
  linarith [show M*(w.re-(1-w.re)) = 2*M*(w.re-1/2) by ring]

theorem dottie_joint_ring_budget_of_horizontal_slope {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (hcont : ContinuousOn (dottieOmittedHorizontal w.im) (Icc (1-w.re) w.re))
    (hdiff : DifferentiableOn ℝ (dottieOmittedHorizontal w.im) (Ioo (1-w.re) w.re))
    (hslope : ∀ r ∈ Ioo (1-w.re) w.re,
      deriv (dottieOmittedHorizontal w.im) r ≤ 94*dottieCircleReference) :
    (dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w).im ≤
      188*((w.re-1/2)*dottieCircleReference) := by
  have hball := Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le
  have hx := archivedRightDisk_horizontal_gap hball
  have hσ := Complex.abs_re_le_norm (w-archivedRightCenter dottieHeight)
  have hh : ‖w-archivedRightCenter dottieHeight‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  rw [hh] at hσ
  have hw₁ : w.re < 1 := by
    have hb := (abs_le.mp hσ).2
    norm_num [archivedRightCenter] at hb
    linarith
  have hs := dottie_joint_omitted_im_le_of_horizontal_slope (by linarith) hw₁
    (94*dottieCircleReference) hcont hdiff hslope
  convert hs using 1
  ring

#print axioms dottie_joint_omitted_eq_two_sides
#print axioms dottie_joint_omitted_im_le_of_horizontal_slope
#print axioms dottie_joint_ring_budget_of_horizontal_slope

end QuarticModel
