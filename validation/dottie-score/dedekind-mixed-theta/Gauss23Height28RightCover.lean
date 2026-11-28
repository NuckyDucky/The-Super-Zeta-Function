import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 28. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell119 : gauss23RightCheck 28 119 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell120 : gauss23RightCheck 28 120 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell121 : gauss23RightCheck 28 121 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell122 : gauss23RightCheck 28 122 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell123 : gauss23RightCheck 28 123 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell124 : gauss23RightCheck 28 124 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell125 : gauss23RightCheck 28 125 = true := by
  decide +kernel

theorem gauss23_right_checks_at_28 (j : Fin 7) :
    gauss23RightCheck 28 (119 + j.val) = true := by
  fin_cases j

  · exact checkCell119
  · exact checkCell120
  · exact checkCell121
  · exact checkCell122
  · exact checkCell123
  · exact checkCell124
  · exact checkCell125

#print axioms gauss23_right_checks_at_28

end FieldTarget
