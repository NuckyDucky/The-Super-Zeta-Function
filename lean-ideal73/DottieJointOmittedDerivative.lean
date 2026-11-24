import DottieRangeDifferentiation
import DottieSharpBlockDerivative
import DottieOmittedHorizontalSlope

/-! The horizontal derivative for the reflected sharp and smoothed middle
blocks, with the original Dottie circle normalization. -/
namespace QuarticModel

open Complex Finset Set
open SuperZeta.StirlingCorrection
open private dottieMiddleNorms from DottieOmittedHorizontalSlope

noncomputable def dottieJointOmittedDerivative (w : ℂ) : ℂ :=
  let h := dottiePrefixEnd
  let len := dottieOmittedSharpEnd-dottiePrefixEnd
  dottieSharpFactor w *
    (((Real.log archivedThetaScale : ℂ)+digamma w-(Real.log (h : ℝ) : ℂ)) *
      dottieNormBlock h len w - dottieCenteredLogBlock h len w) +
    dottieRangeSideDerivative dottieMiddleNorms w

theorem dottie_joint_omitted_hasDerivAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt dottieJointOmittedSide (dottieJointOmittedDerivative w) w := by
  have hS : ∀ n ∈ dottieMiddleNorms, n ≠ 0 := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2.1
    omega
  exact (dottie_completed_norm_block_hasDerivAt dottiePrefixEnd
    (dottieOmittedSharpEnd-dottiePrefixEnd) hw).add
    (dottie_range_side_hasDerivAt _ (by linarith : 0 < w.re+1) hS)

theorem dottie_omitted_horizontal_hasDerivAt (t r : ℝ) (hr : 0 < r) :
    HasDerivAt (dottieOmittedHorizontal t) (dottieJointOmittedDerivative ⟨r,t⟩).im r := by
  have he (x : ℝ) : (⟨x,t⟩ : ℂ) = (x : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  have hd := dottie_joint_omitted_hasDerivAt (w := ⟨r,t⟩) hr
  have hz : HasDerivAt (fun v : ℂ => dottieJointOmittedSide (v+(t : ℂ)*I))
      (dottieJointOmittedDerivative ⟨r,t⟩) (r : ℂ) := by
    have hc : HasDerivAt dottieJointOmittedSide (dottieJointOmittedDerivative ⟨r,t⟩)
        ((r : ℂ)+(t : ℂ)*I) := by
      rwa [← he r]
    simpa only [Function.comp_def, id_eq, mul_one] using
      hc.comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).add_const ((t : ℂ)*I))
  have hg := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hz.comp_ofReal
  change HasDerivAt (fun x : ℝ => (dottieJointOmittedSide ((x : ℂ)+(t : ℂ)*I)).im)
    (dottieJointOmittedDerivative ⟨r,t⟩).im r at hg
  have he' : (fun x : ℝ => (dottieJointOmittedSide ((x : ℂ)+(t : ℂ)*I)).im) =
      dottieOmittedHorizontal t := by
    funext x
    rw [← he x]
    rfl
  rwa [he'] at hg

theorem dottie_joint_ring_budget_of_signed_derivative {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (hslope : ∀ r ∈ Ioo (1-w.re) w.re,
      (dottieJointOmittedDerivative ⟨r,w.im⟩).im ≤ 94*dottieCircleReference) :
    (dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w).im ≤
      188*((w.re-1/2)*dottieCircleReference) := by
  have hdist : ‖w-archivedRightCenter dottieHeight‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm
    (w-archivedRightCenter dottieHeight)).trans_eq hdist)).2
  have hw₁ : w.re < 1 := by
    norm_num [archivedRightCenter] at hre
    linarith
  have hD (r : ℝ) (hr : r ∈ Icc (1-w.re) w.re) :=
    dottie_omitted_horizontal_hasDerivAt w.im r (by linarith [hr.1])
  apply dottie_joint_ring_budget_of_horizontal_slope hw
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · exact fun r hr => (hD r ⟨hr.1.le,hr.2.le⟩).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [(hD r ⟨hr.1.le,hr.2.le⟩).deriv]
    exact hslope r hr

#print axioms dottie_joint_omitted_hasDerivAt
#print axioms dottie_omitted_horizontal_hasDerivAt
#print axioms dottie_joint_ring_budget_of_signed_derivative

end QuarticModel
