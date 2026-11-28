import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 23. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell40 : gauss23RightCheck 23 40 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell41 : gauss23RightCheck 23 41 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell42 : gauss23RightCheck 23 42 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell43 : gauss23RightCheck 23 43 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell44 : gauss23RightCheck 23 44 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell45 : gauss23RightCheck 23 45 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell46 : gauss23RightCheck 23 46 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell47 : gauss23RightCheck 23 47 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell48 : gauss23RightCheck 23 48 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell49 : gauss23RightCheck 23 49 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell50 : gauss23RightCheck 23 50 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell51 : gauss23RightCheck 23 51 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell52 : gauss23RightCheck 23 52 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell53 : gauss23RightCheck 23 53 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell54 : gauss23RightCheck 23 54 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell55 : gauss23RightCheck 23 55 = true := by
  decide +kernel

theorem gauss23_right_checks_at_23 (j : Fin 16) :
    gauss23RightCheck 23 (40 + j.val) = true := by
  fin_cases j

  · exact checkCell40
  · exact checkCell41
  · exact checkCell42
  · exact checkCell43
  · exact checkCell44
  · exact checkCell45
  · exact checkCell46
  · exact checkCell47
  · exact checkCell48
  · exact checkCell49
  · exact checkCell50
  · exact checkCell51
  · exact checkCell52
  · exact checkCell53
  · exact checkCell54
  · exact checkCell55

#print axioms gauss23_right_checks_at_23

end FieldTarget
