import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 12. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell32 :
    (gauss23TwentyCover 32).check (gauss23TwentyValue 12) 32 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell33 :
    (gauss23TwentyCover 33).check (gauss23TwentyValue 12) 33 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell34 :
    (gauss23TwentyCover 34).check (gauss23TwentyValue 12) 34 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell35 :
    (gauss23TwentyCover 35).check (gauss23TwentyValue 12) 35 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell36 :
    (gauss23TwentyCover 36).check (gauss23TwentyValue 12) 36 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell37 :
    (gauss23TwentyCover 37).check (gauss23TwentyValue 12) 37 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell38 :
    (gauss23TwentyCover 38).check (gauss23TwentyValue 12) 38 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell39 :
    (gauss23TwentyCover 39).check (gauss23TwentyValue 12) 39 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell40 :
    (gauss23TwentyCover 40).check (gauss23TwentyValue 12) 40 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell41 :
    (gauss23TwentyCover 41).check (gauss23TwentyValue 12) 41 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell42 :
    (gauss23TwentyCover 42).check (gauss23TwentyValue 12) 42 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell43 :
    (gauss23TwentyCover 43).check (gauss23TwentyValue 12) 43 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell44 :
    (gauss23TwentyCover 44).check (gauss23TwentyValue 12) 44 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell45 :
    (gauss23TwentyCover 45).check (gauss23TwentyValue 12) 45 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell46 :
    (gauss23TwentyCover 46).check (gauss23TwentyValue 12) 46 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell47 :
    (gauss23TwentyCover 47).check (gauss23TwentyValue 12) 47 = true := by
  decide +kernel

theorem gauss23_checks_at_12 (j : Fin 16) :
    (gauss23TwentyCover (32 + j.val)).check (gauss23TwentyValue 12) (32 + j.val) = true := by
  fin_cases j

  · exact checkCell32
  · exact checkCell33
  · exact checkCell34
  · exact checkCell35
  · exact checkCell36
  · exact checkCell37
  · exact checkCell38
  · exact checkCell39
  · exact checkCell40
  · exact checkCell41
  · exact checkCell42
  · exact checkCell43
  · exact checkCell44
  · exact checkCell45
  · exact checkCell46
  · exact checkCell47

#print axioms gauss23_checks_at_12

end FieldTarget
