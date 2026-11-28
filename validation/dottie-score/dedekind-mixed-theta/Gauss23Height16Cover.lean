import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 16. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell96 :
    (gauss23TwentyCover 96).check (gauss23TwentyValue 16) 96 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell97 :
    (gauss23TwentyCover 97).check (gauss23TwentyValue 16) 97 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell98 :
    (gauss23TwentyCover 98).check (gauss23TwentyValue 16) 98 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell99 :
    (gauss23TwentyCover 99).check (gauss23TwentyValue 16) 99 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell100 :
    (gauss23TwentyCover 100).check (gauss23TwentyValue 16) 100 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell101 :
    (gauss23TwentyCover 101).check (gauss23TwentyValue 16) 101 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell102 :
    (gauss23TwentyCover 102).check (gauss23TwentyValue 16) 102 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell103 :
    (gauss23TwentyCover 103).check (gauss23TwentyValue 16) 103 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell104 :
    (gauss23TwentyCover 104).check (gauss23TwentyValue 16) 104 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell105 :
    (gauss23TwentyCover 105).check (gauss23TwentyValue 16) 105 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell106 :
    (gauss23TwentyCover 106).check (gauss23TwentyValue 16) 106 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell107 :
    (gauss23TwentyCover 107).check (gauss23TwentyValue 16) 107 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell108 :
    (gauss23TwentyCover 108).check (gauss23TwentyValue 16) 108 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell109 :
    (gauss23TwentyCover 109).check (gauss23TwentyValue 16) 109 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell110 :
    (gauss23TwentyCover 110).check (gauss23TwentyValue 16) 110 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell111 :
    (gauss23TwentyCover 111).check (gauss23TwentyValue 16) 111 = true := by
  decide +kernel

theorem gauss23_checks_at_16 (j : Fin 16) :
    (gauss23TwentyCover (96 + j.val)).check (gauss23TwentyValue 16) (96 + j.val) = true := by
  fin_cases j

  · exact checkCell96
  · exact checkCell97
  · exact checkCell98
  · exact checkCell99
  · exact checkCell100
  · exact checkCell101
  · exact checkCell102
  · exact checkCell103
  · exact checkCell104
  · exact checkCell105
  · exact checkCell106
  · exact checkCell107
  · exact checkCell108
  · exact checkCell109
  · exact checkCell110
  · exact checkCell111

#print axioms gauss23_checks_at_16

end FieldTarget
