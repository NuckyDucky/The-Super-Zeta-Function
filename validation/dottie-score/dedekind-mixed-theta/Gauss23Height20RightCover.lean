import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 20. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell0 : gauss23RightCheck 20 0 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell1 : gauss23RightCheck 20 1 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell2 : gauss23RightCheck 20 2 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell3 : gauss23RightCheck 20 3 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell4 : gauss23RightCheck 20 4 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell5 : gauss23RightCheck 20 5 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell6 : gauss23RightCheck 20 6 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell7 : gauss23RightCheck 20 7 = true := by
  decide +kernel

theorem gauss23_right_checks_at_20 (j : Fin 8) :
    gauss23RightCheck 20 (0 + j.val) = true := by
  fin_cases j

  · exact checkCell0
  · exact checkCell1
  · exact checkCell2
  · exact checkCell3
  · exact checkCell4
  · exact checkCell5
  · exact checkCell6
  · exact checkCell7

#print axioms gauss23_right_checks_at_20

end FieldTarget
