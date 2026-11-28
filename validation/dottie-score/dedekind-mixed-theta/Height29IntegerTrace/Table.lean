import Height29IntegerTrace.Data00
import Height29IntegerTrace.Data01
import Height29IntegerTrace.Data02
import Height29IntegerTrace.Data03
import Height29IntegerTrace.Data04
import Height29IntegerTrace.Data05
import Height29IntegerTrace.Data06
import Height29IntegerTrace.Data07
import Height29IntegerTrace.Seeds

namespace FieldTarget

private def allTraceData : Array (Array (Array GaussPanelTrace)) :=
  #[height29TraceData00, height29TraceData01, height29TraceData02, height29TraceData03,
    height29TraceData04, height29TraceData05, height29TraceData06, height29TraceData07]

def height29GaussTrace (p : Fin 32) (i : Fin 24) : GaussPanelTrace :=
  let panelBlock := allTraceData[p.val / 4]!
  let panel := panelBlock[p.val % 4]!
  panel[i.val]!

def height29GaussTraceIndex (group : Fin 8) (slot : Fin 4) : Fin 32 :=
  ⟨4 * group.val + slot.val, by omega⟩

end FieldTarget
