import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 17. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell112 :
    (gauss23TwentyCover 112).check (gauss23TwentyValue 17) 112 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell113 :
    (gauss23TwentyCover 113).check (gauss23TwentyValue 17) 113 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell114 :
    (gauss23TwentyCover 114).check (gauss23TwentyValue 17) 114 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell115 :
    (gauss23TwentyCover 115).check (gauss23TwentyValue 17) 115 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell116 :
    (gauss23TwentyCover 116).check (gauss23TwentyValue 17) 116 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell117 :
    (gauss23TwentyCover 117).check (gauss23TwentyValue 17) 117 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell118 :
    (gauss23TwentyCover 118).check (gauss23TwentyValue 17) 118 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell119 :
    (gauss23TwentyCover 119).check (gauss23TwentyValue 17) 119 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell120 :
    (gauss23TwentyCover 120).check (gauss23TwentyValue 17) 120 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell121 :
    (gauss23TwentyCover 121).check (gauss23TwentyValue 17) 121 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell122 :
    (gauss23TwentyCover 122).check (gauss23TwentyValue 17) 122 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell123 :
    (gauss23TwentyCover 123).check (gauss23TwentyValue 17) 123 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell124 :
    (gauss23TwentyCover 124).check (gauss23TwentyValue 17) 124 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell125 :
    (gauss23TwentyCover 125).check (gauss23TwentyValue 17) 125 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell126 :
    (gauss23TwentyCover 126).check (gauss23TwentyValue 17) 126 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell127 :
    (gauss23TwentyCover 127).check (gauss23TwentyValue 17) 127 = true := by
  decide +kernel

theorem gauss23_checks_at_17 (j : Fin 16) :
    (gauss23TwentyCover (112 + j.val)).check (gauss23TwentyValue 17) (112 + j.val) = true := by
  fin_cases j

  · exact checkCell112
  · exact checkCell113
  · exact checkCell114
  · exact checkCell115
  · exact checkCell116
  · exact checkCell117
  · exact checkCell118
  · exact checkCell119
  · exact checkCell120
  · exact checkCell121
  · exact checkCell122
  · exact checkCell123
  · exact checkCell124
  · exact checkCell125
  · exact checkCell126
  · exact checkCell127

#print axioms gauss23_checks_at_17

end FieldTarget
