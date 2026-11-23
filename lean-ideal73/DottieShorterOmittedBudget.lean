import DottieReferenceQuantitative
import DottieLowerFullBudget

/-! Place the earlier absolute cutoff in the signed budget of the same
archived circle. The signed terms retain both reflected Gaussian sheets. -/

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
set_option autoImplicit false

def dottieEarlierFarCut : ℕ := 8*10^24

noncomputable def dottieShorterMiddleSmooth (w : ℂ) : ℂ :=
  ∑ n ∈ dottieOmittedNorms.filter (fun n => dottieOmittedSharpEnd < n ∧ n ≤ dottieEarlierFarCut),
    dottieSmoothTerm w n

noncomputable def dottieEarlierFarSmooth (w : ℂ) : ℂ :=
  ∑ n ∈ dottieOmittedNorms.filter (fun n => dottieEarlierFarCut < n), dottieSmoothTerm w n

theorem dottie_middle_add_far_eq_shorter_split (w : ℂ) :
    dottieOmittedMiddleSmooth w + dottieOmittedFarSmooth w =
      dottieShorterMiddleSmooth w + dottieEarlierFarSmooth w := by
  have hsharp : dottieOmittedSharpEnd ≤ dottieEarlierFarCut := by decide +kernel
  have hfar : dottieEarlierFarCut ≤ dottieOmittedFarCut := by decide +kernel
  unfold dottieOmittedMiddleSmooth dottieOmittedFarSmooth
    dottieShorterMiddleSmooth dottieEarlierFarSmooth
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rcases le_or_gt n dottieOmittedSharpEnd with hn | hn
  · simp [hn.not_gt, (hn.trans hsharp).not_gt, (hn.trans (hsharp.trans hfar)).not_gt]
  · rcases le_or_gt n dottieEarlierFarCut with hx | hx
    · simp [hn, hx, hx.not_gt, (hx.trans hfar).not_gt, hx.trans hfar]
    · rcases le_or_gt n dottieOmittedFarCut with hy | hy
      · simp [hn, hx, not_le_of_gt hx, hy, hy.not_gt]
      · simp [hn, hx, not_le_of_gt hx, hy, not_le_of_gt hy]

theorem dottie_earlier_far_budget_of_reference_lower
    (hS : 2/10^30 ≤ dottieCircleReference) {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieEarlierFarSmooth w‖ ≤ (465/1000)*((w.re-1/2)*dottieCircleReference) := by
  obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hbound : ‖dottieEarlierFarSmooth w‖ ≤ 2/(5*10^33) :=
    dottie_smooth_subset_uniform_absolute _ (fun _ hn => (Finset.mem_filter.mp hn).2) hr hi
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hprod := mul_le_mul hx hS (by norm_num) (by linarith only [hx])
  exact hbound.trans (by nlinarith only [hprod])

/-- The same circle contradiction now needs the joint signed inequality
only through `8 * 10^24`. The rest is included in the absolute budget. -/
theorem dottie_omitted_budget_of_shorter_signed_block
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 =
      dottiePairedCandidateTicks)
    (hsigned : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w).im ≤
        188*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    (dottieOmitted w).im ≤ 189*((w.re-1/2)*dottieCircleReference) := by
  have hS := dottieCircleReference_lower_of_candidate_equality hscore
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hscale : 0 ≤ (w.re-1/2)*dottieCircleReference :=
    mul_nonneg (by linarith only [hx]) (by linarith only [hS])
  have hl := (le_abs_self (dottieOmittedLowerSmoothingError w).im).trans
    ((Complex.abs_im_le_norm _).trans (dottie_lower_omitted_budget_of_candidate_equality hscore hw))
  have hf := (le_abs_self (dottieEarlierFarSmooth w).im).trans
    ((Complex.abs_im_le_norm _).trans (dottie_earlier_far_budget_of_reference_lower hS hw))
  have hsplit : dottieOmitted w = (dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w) +
      dottieOmittedLowerSmoothingError w + dottieEarlierFarSmooth w := by
    rw [dottieOmitted_eq_sharp_add_middle_add_errors]
    calc
      _ = dottieOmittedSharpBlock w + (dottieOmittedMiddleSmooth w+dottieOmittedFarSmooth w) +
          dottieOmittedLowerSmoothingError w := by abel
      _ = _ := by rw [dottie_middle_add_far_eq_shorter_split]; abel
  rw [hsplit, Complex.add_im, Complex.add_im]
  linarith only [hsigned w hw, hl, hf, hscale]

#print axioms dottie_middle_add_far_eq_shorter_split
#print axioms dottie_earlier_far_budget_of_reference_lower
#print axioms dottie_omitted_budget_of_shorter_signed_block

end QuarticModel
