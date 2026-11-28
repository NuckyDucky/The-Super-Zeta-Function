import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 25. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell72 : gauss23RightCheck 25 72 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell73 : gauss23RightCheck 25 73 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell74 : gauss23RightCheck 25 74 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell75 : gauss23RightCheck 25 75 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell76 : gauss23RightCheck 25 76 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell77 : gauss23RightCheck 25 77 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell78 : gauss23RightCheck 25 78 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell79 : gauss23RightCheck 25 79 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell80 : gauss23RightCheck 25 80 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell81 : gauss23RightCheck 25 81 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell82 : gauss23RightCheck 25 82 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell83 : gauss23RightCheck 25 83 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell84 : gauss23RightCheck 25 84 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell85 : gauss23RightCheck 25 85 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell86 : gauss23RightCheck 25 86 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell87 : gauss23RightCheck 25 87 = true := by
  decide +kernel

theorem gauss23_right_checks_at_25 (j : Fin 16) :
    gauss23RightCheck 25 (72 + j.val) = true := by
  fin_cases j

  · exact checkCell72
  · exact checkCell73
  · exact checkCell74
  · exact checkCell75
  · exact checkCell76
  · exact checkCell77
  · exact checkCell78
  · exact checkCell79
  · exact checkCell80
  · exact checkCell81
  · exact checkCell82
  · exact checkCell83
  · exact checkCell84
  · exact checkCell85
  · exact checkCell86
  · exact checkCell87

#print axioms gauss23_right_checks_at_25

end FieldTarget
