import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 20. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell160 :
    (gauss23TwentyCover 160).check (gauss23TwentyValue 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell161 :
    (gauss23TwentyCover 161).check (gauss23TwentyValue 20) 161 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell162 :
    (gauss23TwentyCover 162).check (gauss23TwentyValue 20) 162 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell163 :
    (gauss23TwentyCover 163).check (gauss23TwentyValue 20) 163 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell164 :
    (gauss23TwentyCover 164).check (gauss23TwentyValue 20) 164 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell165 :
    (gauss23TwentyCover 165).check (gauss23TwentyValue 20) 165 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell166 :
    (gauss23TwentyCover 166).check (gauss23TwentyValue 20) 166 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell167 :
    (gauss23TwentyCover 167).check (gauss23TwentyValue 20) 167 = true := by
  decide +kernel

theorem gauss23_checks_at_20 (j : Fin 8) :
    (gauss23TwentyCover (160 + j.val)).check (gauss23TwentyValue 20) (160 + j.val) = true := by
  fin_cases j

  · exact checkCell160
  · exact checkCell161
  · exact checkCell162
  · exact checkCell163
  · exact checkCell164
  · exact checkCell165
  · exact checkCell166
  · exact checkCell167

#print axioms gauss23_checks_at_20

end FieldTarget
