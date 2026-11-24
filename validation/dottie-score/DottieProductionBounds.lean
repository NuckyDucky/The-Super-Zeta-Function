import DottieProductionJoined
import DottieReferenceQuantitative

namespace QuarticModel

open SuperZeta.StirlingCorrection

theorem dottieProductionCircleReference_lower : 2 / 10^30 ≤ dottieCircleReference :=
  dottieCircleReference_lower_of_candidate_equality dottieProductionFullSpan_eq_candidate

theorem dottieProductionCircleScale_lower {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048)) :
    (1 / 2048 : ℝ) * (2 / 10^30) ≤ (w.re - 1 / 2) * dottieCircleReference := by
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  exact mul_le_mul hx dottieProductionCircleReference_lower (by positivity) (by linarith)

theorem dottieProductionFarSmooth_budget {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048)) :
    ‖dottieOmittedFarSmooth w‖ ≤ (465 / 1000) * ((w.re - 1 / 2) * dottieCircleReference) :=
  dottie_far_budget_of_candidate_equality dottieProductionFullSpan_eq_candidate hw

#print axioms dottieProductionCircleReference_lower
#print axioms dottieProductionCircleScale_lower
#print axioms dottieProductionFarSmooth_budget

end QuarticModel
