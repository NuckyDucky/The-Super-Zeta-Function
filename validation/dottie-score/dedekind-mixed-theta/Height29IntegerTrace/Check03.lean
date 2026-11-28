import Height29IntegerTrace.Table

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_12_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 3 0) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_13_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 3 1) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_14_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 3 2) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_15_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 3 3) i := by
  decide +kernel

theorem height29_gauss_trace_block_03 (j : Fin 4) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 3 j) i := by
  fin_cases j
  · exact panel_12_checked i
  · exact panel_13_checked i
  · exact panel_14_checked i
  · exact panel_15_checked i

#print axioms height29_gauss_trace_block_03

end FieldTarget
