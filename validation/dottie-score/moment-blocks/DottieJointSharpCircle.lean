import DottieDirectReference
import DottieJointMomentScore

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection

set_option autoImplicit false

/-- Check the eleven sharp boxes from the integer tick pairs. -/
def dottieSharpScoresFit (ticks : List (ℤ × ℤ)) : Bool :=
  (List.range 11).all fun k =>
    let t := ticks.getD k (0,0)
    (momentScoreRect t.1 t.2 k (8/10^8)).fits (fixedSharpInput k)

/-- The joint totals enter the original circle proof with its uniform rounding allowance. -/
theorem dottie_sharp_margin_of_joint_scores (ticks : List (ℤ × ℤ))
    (hTotals : ∀ k : Fin 11,
      dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightRealTicks n k) 0 dottiePrefixEnd.sqrt =
        (ticks.getD k (0,0)).1 ∧
      dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightImagTicks n k) 0 dottiePrefixEnd.sqrt =
        (ticks.getD k (0,0)).2)
    (hFit : dottieSharpScoresFit ticks = true)
    (hReference : dottieRelativeReferenceProjection ≤ 171687/10^6) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_margin_of_decimal_reference _ hReference
  intro k hk
  obtain ⟨hre, him⟩ := hTotals ⟨k,hk⟩
  change dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightRealTicks n k) 0
    dottiePrefixEnd.sqrt = (ticks.getD k (0,0)).1 at hre
  change dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightImagTicks n k) 0
    dottiePrefixEnd.sqrt = (ticks.getD k (0,0)).2 at him
  rw [archivedScoredMomentBox, hre, him]
  exact List.all_eq_true.mp hFit k (List.mem_range.mpr hk)

#print axioms dottie_sharp_margin_of_joint_scores

end QuarticModel.DottieFixedIntervals
