import Height29IntegerTrace.Check00
import Height29IntegerTrace.Check01
import Height29IntegerTrace.Check02
import Height29IntegerTrace.Check03
import Height29IntegerTrace.Check04
import Height29IntegerTrace.Check05
import Height29IntegerTrace.Check06
import Height29IntegerTrace.Check07
import Height29IntegerTrace.SeedsChecked

namespace FieldTarget

theorem height29_gauss_trace_checked (p : Fin 32) (i : Fin 24) :
    GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep height29GaussTrace p i := by
  have h (g : Fin 8) (s : Fin 4) :
      GaussPanelTraceAgrees height29ArchivedInitialPhase height29ArchivedPhaseStep height29GaussTrace
        (height29GaussTraceIndex g s) i := by
    fin_cases g
    · exact height29_gauss_trace_block_00 s i
    · exact height29_gauss_trace_block_01 s i
    · exact height29_gauss_trace_block_02 s i
    · exact height29_gauss_trace_block_03 s i
    · exact height29_gauss_trace_block_04 s i
    · exact height29_gauss_trace_block_05 s i
    · exact height29_gauss_trace_block_06 s i
    · exact height29_gauss_trace_block_07 s i
  let g : Fin 8 := ⟨p.val / 4, by omega⟩
  let s : Fin 4 := ⟨p.val % 4, by omega⟩
  have heq : height29GaussTraceIndex g s = p := by
    apply Fin.ext
    dsimp only [height29GaussTraceIndex, g, s]
    omega
  simpa only [heq] using h g s

theorem height29_gauss_trace_approximations (p : Fin 32) (i : Fin 24) :
    (height29GaussTrace p i).approximation = gaussPanelApproximation p.val i :=
  gaussTraceApproximations_eq height29_initial_phases_checked height29_phase_step_checked
    height29_gauss_trace_checked p i

#print axioms height29_gauss_trace_approximations

end FieldTarget
