import DottieNormalizedMomentScore

namespace QuarticModel.DottieFixedIntervals

def momentPilotBox : Rect :=
  ⟨⟨15753519438947957080,15790412927095376184⟩,
    ⟨12746700154933300166,12783593643080719270⟩⟩

theorem momentPilot_at_two :
    momentPilotBox.Contains (signedMoment archivedLatticeCoeff 2 dottieSharpCenter 0) := by
  apply archivedMomentBox_of_scores
    (r := 15773344598623970292) (i := 12766915003519110527)
  · decide +kernel
  · intro n hn hN
    have h : n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms momentPilot_at_two

end QuarticModel.DottieFixedIntervals
