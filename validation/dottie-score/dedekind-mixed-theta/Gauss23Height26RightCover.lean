import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 26. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell88 : gauss23RightCheck 26 88 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell89 : gauss23RightCheck 26 89 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell90 : gauss23RightCheck 26 90 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell91 : gauss23RightCheck 26 91 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell92 : gauss23RightCheck 26 92 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell93 : gauss23RightCheck 26 93 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell94 : gauss23RightCheck 26 94 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell95 : gauss23RightCheck 26 95 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell96 : gauss23RightCheck 26 96 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell97 : gauss23RightCheck 26 97 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell98 : gauss23RightCheck 26 98 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell99 : gauss23RightCheck 26 99 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell100 : gauss23RightCheck 26 100 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell101 : gauss23RightCheck 26 101 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell102 : gauss23RightCheck 26 102 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell103 : gauss23RightCheck 26 103 = true := by
  decide +kernel

theorem gauss23_right_checks_at_26 (j : Fin 16) :
    gauss23RightCheck 26 (88 + j.val) = true := by
  fin_cases j

  · exact checkCell88
  · exact checkCell89
  · exact checkCell90
  · exact checkCell91
  · exact checkCell92
  · exact checkCell93
  · exact checkCell94
  · exact checkCell95
  · exact checkCell96
  · exact checkCell97
  · exact checkCell98
  · exact checkCell99
  · exact checkCell100
  · exact checkCell101
  · exact checkCell102
  · exact checkCell103

#print axioms gauss23_right_checks_at_26

end FieldTarget
