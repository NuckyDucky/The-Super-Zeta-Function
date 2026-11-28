import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 18. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell128 :
    (gauss23TwentyCover 128).check (gauss23TwentyValue 18) 128 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell129 :
    (gauss23TwentyCover 129).check (gauss23TwentyValue 18) 129 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell130 :
    (gauss23TwentyCover 130).check (gauss23TwentyValue 18) 130 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell131 :
    (gauss23TwentyCover 131).check (gauss23TwentyValue 18) 131 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell132 :
    (gauss23TwentyCover 132).check (gauss23TwentyValue 18) 132 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell133 :
    (gauss23TwentyCover 133).check (gauss23TwentyValue 18) 133 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell134 :
    (gauss23TwentyCover 134).check (gauss23TwentyValue 18) 134 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell135 :
    (gauss23TwentyCover 135).check (gauss23TwentyValue 18) 135 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell136 :
    (gauss23TwentyCover 136).check (gauss23TwentyValue 18) 136 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell137 :
    (gauss23TwentyCover 137).check (gauss23TwentyValue 18) 137 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell138 :
    (gauss23TwentyCover 138).check (gauss23TwentyValue 18) 138 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell139 :
    (gauss23TwentyCover 139).check (gauss23TwentyValue 18) 139 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell140 :
    (gauss23TwentyCover 140).check (gauss23TwentyValue 18) 140 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell141 :
    (gauss23TwentyCover 141).check (gauss23TwentyValue 18) 141 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell142 :
    (gauss23TwentyCover 142).check (gauss23TwentyValue 18) 142 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell143 :
    (gauss23TwentyCover 143).check (gauss23TwentyValue 18) 143 = true := by
  decide +kernel

theorem gauss23_checks_at_18 (j : Fin 16) :
    (gauss23TwentyCover (128 + j.val)).check (gauss23TwentyValue 18) (128 + j.val) = true := by
  fin_cases j

  · exact checkCell128
  · exact checkCell129
  · exact checkCell130
  · exact checkCell131
  · exact checkCell132
  · exact checkCell133
  · exact checkCell134
  · exact checkCell135
  · exact checkCell136
  · exact checkCell137
  · exact checkCell138
  · exact checkCell139
  · exact checkCell140
  · exact checkCell141
  · exact checkCell142
  · exact checkCell143

#print axioms gauss23_checks_at_18

end FieldTarget
