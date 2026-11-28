import Height29IntegerTrace.Table

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_4_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 1 0) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_5_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 1 1) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_6_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 1 2) i := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem panel_7_checked :
    ∀ i : Fin 24, GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 1 3) i := by
  decide +kernel

theorem height29_gauss_trace_block_01 (j : Fin 4) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep
      height29GaussTrace (height29GaussTraceIndex 1 j) i := by
  fin_cases j
  · exact panel_4_checked i
  · exact panel_5_checked i
  · exact panel_6_checked i
  · exact panel_7_checked i

#print axioms height29_gauss_trace_block_01

end FieldTarget
