import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 22. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell24 : gauss23RightCheck 22 24 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell25 : gauss23RightCheck 22 25 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell26 : gauss23RightCheck 22 26 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell27 : gauss23RightCheck 22 27 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell28 : gauss23RightCheck 22 28 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell29 : gauss23RightCheck 22 29 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell30 : gauss23RightCheck 22 30 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell31 : gauss23RightCheck 22 31 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell32 : gauss23RightCheck 22 32 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell33 : gauss23RightCheck 22 33 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell34 : gauss23RightCheck 22 34 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell35 : gauss23RightCheck 22 35 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell36 : gauss23RightCheck 22 36 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell37 : gauss23RightCheck 22 37 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell38 : gauss23RightCheck 22 38 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell39 : gauss23RightCheck 22 39 = true := by
  decide +kernel

theorem gauss23_right_checks_at_22 (j : Fin 16) :
    gauss23RightCheck 22 (24 + j.val) = true := by
  fin_cases j

  · exact checkCell24
  · exact checkCell25
  · exact checkCell26
  · exact checkCell27
  · exact checkCell28
  · exact checkCell29
  · exact checkCell30
  · exact checkCell31
  · exact checkCell32
  · exact checkCell33
  · exact checkCell34
  · exact checkCell35
  · exact checkCell36
  · exact checkCell37
  · exact checkCell38
  · exact checkCell39

#print axioms gauss23_right_checks_at_22

end FieldTarget
