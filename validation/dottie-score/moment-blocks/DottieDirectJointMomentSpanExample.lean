import DottieDirectJointMomentSpans
import DottieFullSharpRows

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000

/-- The direct evaluator recovers the archived table on two complete adjacent rows. -/
theorem dottie_direct_joint_moment_two_rows :
    dottieDirectJointMomentSpan 11 1442840576 100 2 = dottieSharpRows100To102Ticks := by
  have h := dottie_direct_joint_moment_span_agrees 11 1442840576 100 2
  apply List.ext_getElem
  · exact h.1.trans (by decide +kernel)
  · intro k hd ht
    have hk : k < 11 := by simpa only [h.1] using hd
    rw [List.getElem_eq_getD (h := hd) (0,0), List.getElem_eq_getD (h := ht) (0,0)]
    exact (h.2 k hk).trans (dottie_sharp_rows100To102_complete ⟨k,hk⟩).symm

#print axioms dottie_direct_joint_moment_two_rows

end QuarticModel.DottieFixedIntervals
