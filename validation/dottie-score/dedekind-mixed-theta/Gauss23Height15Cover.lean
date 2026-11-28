import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 15. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell80 :
    (gauss23TwentyCover 80).check (gauss23TwentyValue 15) 80 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell81 :
    (gauss23TwentyCover 81).check (gauss23TwentyValue 15) 81 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell82 :
    (gauss23TwentyCover 82).check (gauss23TwentyValue 15) 82 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell83 :
    (gauss23TwentyCover 83).check (gauss23TwentyValue 15) 83 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell84 :
    (gauss23TwentyCover 84).check (gauss23TwentyValue 15) 84 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell85 :
    (gauss23TwentyCover 85).check (gauss23TwentyValue 15) 85 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell86 :
    (gauss23TwentyCover 86).check (gauss23TwentyValue 15) 86 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell87 :
    (gauss23TwentyCover 87).check (gauss23TwentyValue 15) 87 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell88 :
    (gauss23TwentyCover 88).check (gauss23TwentyValue 15) 88 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell89 :
    (gauss23TwentyCover 89).check (gauss23TwentyValue 15) 89 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell90 :
    (gauss23TwentyCover 90).check (gauss23TwentyValue 15) 90 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell91 :
    (gauss23TwentyCover 91).check (gauss23TwentyValue 15) 91 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell92 :
    (gauss23TwentyCover 92).check (gauss23TwentyValue 15) 92 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell93 :
    (gauss23TwentyCover 93).check (gauss23TwentyValue 15) 93 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell94 :
    (gauss23TwentyCover 94).check (gauss23TwentyValue 15) 94 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell95 :
    (gauss23TwentyCover 95).check (gauss23TwentyValue 15) 95 = true := by
  decide +kernel

theorem gauss23_checks_at_15 (j : Fin 16) :
    (gauss23TwentyCover (80 + j.val)).check (gauss23TwentyValue 15) (80 + j.val) = true := by
  fin_cases j

  · exact checkCell80
  · exact checkCell81
  · exact checkCell82
  · exact checkCell83
  · exact checkCell84
  · exact checkCell85
  · exact checkCell86
  · exact checkCell87
  · exact checkCell88
  · exact checkCell89
  · exact checkCell90
  · exact checkCell91
  · exact checkCell92
  · exact checkCell93
  · exact checkCell94
  · exact checkCell95

#print axioms gauss23_checks_at_15

end FieldTarget
