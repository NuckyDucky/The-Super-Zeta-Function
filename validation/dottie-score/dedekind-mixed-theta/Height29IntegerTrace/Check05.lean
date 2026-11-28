import Height29IntegerTrace.Table

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_20_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 5 0) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_21_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 5 1) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_22_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 5 2) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_23_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 5 3) i := by
  decide +kernel

theorem height29_gauss_trace_block_05 (j : Fin 4) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 5 j) i := by
  fin_cases j
  · exact panel_20_checked i
  · exact panel_21_checked i
  · exact panel_22_checked i
  · exact panel_23_checked i

#print axioms height29_gauss_trace_block_05

end FieldTarget
