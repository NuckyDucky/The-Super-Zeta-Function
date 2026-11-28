import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 14. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell64 :
    (gauss23TwentyCover 64).check (gauss23TwentyValue 14) 64 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell65 :
    (gauss23TwentyCover 65).check (gauss23TwentyValue 14) 65 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell66 :
    (gauss23TwentyCover 66).check (gauss23TwentyValue 14) 66 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell67 :
    (gauss23TwentyCover 67).check (gauss23TwentyValue 14) 67 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell68 :
    (gauss23TwentyCover 68).check (gauss23TwentyValue 14) 68 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell69 :
    (gauss23TwentyCover 69).check (gauss23TwentyValue 14) 69 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell70 :
    (gauss23TwentyCover 70).check (gauss23TwentyValue 14) 70 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell71 :
    (gauss23TwentyCover 71).check (gauss23TwentyValue 14) 71 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell72 :
    (gauss23TwentyCover 72).check (gauss23TwentyValue 14) 72 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell73 :
    (gauss23TwentyCover 73).check (gauss23TwentyValue 14) 73 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell74 :
    (gauss23TwentyCover 74).check (gauss23TwentyValue 14) 74 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell75 :
    (gauss23TwentyCover 75).check (gauss23TwentyValue 14) 75 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell76 :
    (gauss23TwentyCover 76).check (gauss23TwentyValue 14) 76 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell77 :
    (gauss23TwentyCover 77).check (gauss23TwentyValue 14) 77 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell78 :
    (gauss23TwentyCover 78).check (gauss23TwentyValue 14) 78 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell79 :
    (gauss23TwentyCover 79).check (gauss23TwentyValue 14) 79 = true := by
  decide +kernel

theorem gauss23_checks_at_14 (j : Fin 16) :
    (gauss23TwentyCover (64 + j.val)).check (gauss23TwentyValue 14) (64 + j.val) = true := by
  fin_cases j

  · exact checkCell64
  · exact checkCell65
  · exact checkCell66
  · exact checkCell67
  · exact checkCell68
  · exact checkCell69
  · exact checkCell70
  · exact checkCell71
  · exact checkCell72
  · exact checkCell73
  · exact checkCell74
  · exact checkCell75
  · exact checkCell76
  · exact checkCell77
  · exact checkCell78
  · exact checkCell79

#print axioms gauss23_checks_at_14

end FieldTarget
