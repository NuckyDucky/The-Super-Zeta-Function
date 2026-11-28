import Height29IntegerTrace.Table

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_8_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 2 0) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_9_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 2 1) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_10_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 2 2) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_11_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 2 3) i := by
  decide +kernel

theorem height29_gauss_trace_block_02 (j : Fin 4) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 2 j) i := by
  fin_cases j
  · exact panel_8_checked i
  · exact panel_9_checked i
  · exact panel_10_checked i
  · exact panel_11_checked i

#print axioms height29_gauss_trace_block_02

end FieldTarget
