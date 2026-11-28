import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 21. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell8 : gauss23RightCheck 21 8 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell9 : gauss23RightCheck 21 9 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell10 : gauss23RightCheck 21 10 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell11 : gauss23RightCheck 21 11 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell12 : gauss23RightCheck 21 12 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell13 : gauss23RightCheck 21 13 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell14 : gauss23RightCheck 21 14 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell15 : gauss23RightCheck 21 15 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell16 : gauss23RightCheck 21 16 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell17 : gauss23RightCheck 21 17 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell18 : gauss23RightCheck 21 18 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell19 : gauss23RightCheck 21 19 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell20 : gauss23RightCheck 21 20 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell21 : gauss23RightCheck 21 21 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell22 : gauss23RightCheck 21 22 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell23 : gauss23RightCheck 21 23 = true := by
  decide +kernel

theorem gauss23_right_checks_at_21 (j : Fin 16) :
    gauss23RightCheck 21 (8 + j.val) = true := by
  fin_cases j

  · exact checkCell8
  · exact checkCell9
  · exact checkCell10
  · exact checkCell11
  · exact checkCell12
  · exact checkCell13
  · exact checkCell14
  · exact checkCell15
  · exact checkCell16
  · exact checkCell17
  · exact checkCell18
  · exact checkCell19
  · exact checkCell20
  · exact checkCell21
  · exact checkCell22
  · exact checkCell23

#print axioms gauss23_right_checks_at_21

end FieldTarget
