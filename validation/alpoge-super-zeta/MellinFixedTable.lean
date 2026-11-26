import MellinFixedFunctions
import MellinIntegerTable

/-! The integer checks read the same sample table used by the Mellin moment certificate. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

open MellinInteger

def checkTableNode (i j : Nat) : Bool :=
  let (re, im) := (fixedColumns (i/64) j).getD (i%64) (0,0)
  checkDensity (coordinateNumerator i j) re im

def checkTablePanel (i : Nat) : Bool :=
  (List.range 25).all (checkTableNode i)

def auditedPanels : List Nat := [576, 2048, 2141, 2272]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
theorem audited_panels_checked : auditedPanels.all checkTablePanel = true := by
  decide +kernel

#print axioms audited_panels_checked

end DottieOriented.NativeSpectrum.MellinFixed
