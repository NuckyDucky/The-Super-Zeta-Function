import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 27. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell104 : gauss23RightCheck 27 104 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell105 : gauss23RightCheck 27 105 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell106 : gauss23RightCheck 27 106 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell107 : gauss23RightCheck 27 107 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell108 : gauss23RightCheck 27 108 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell109 : gauss23RightCheck 27 109 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell110 : gauss23RightCheck 27 110 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell111 : gauss23RightCheck 27 111 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell112 : gauss23RightCheck 27 112 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell113 : gauss23RightCheck 27 113 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell114 : gauss23RightCheck 27 114 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell115 : gauss23RightCheck 27 115 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell116 : gauss23RightCheck 27 116 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell117 : gauss23RightCheck 27 117 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell118 : gauss23RightCheck 27 118 = true := by
  decide +kernel

theorem gauss23_right_checks_at_27 (j : Fin 15) :
    gauss23RightCheck 27 (104 + j.val) = true := by
  fin_cases j

  · exact checkCell104
  · exact checkCell105
  · exact checkCell106
  · exact checkCell107
  · exact checkCell108
  · exact checkCell109
  · exact checkCell110
  · exact checkCell111
  · exact checkCell112
  · exact checkCell113
  · exact checkCell114
  · exact checkCell115
  · exact checkCell116
  · exact checkCell117
  · exact checkCell118

#print axioms gauss23_right_checks_at_27

end FieldTarget
