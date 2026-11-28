import Height29IntegerTrace.Table

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_16_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 4 0) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_17_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 4 1) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_18_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 4 2) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_19_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 4 3) i := by
  decide +kernel

theorem height29_gauss_trace_block_04 (j : Fin 4) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 4 j) i := by
  fin_cases j
  · exact panel_16_checked i
  · exact panel_17_checked i
  · exact panel_18_checked i
  · exact panel_19_checked i

#print axioms height29_gauss_trace_block_04

end FieldTarget
