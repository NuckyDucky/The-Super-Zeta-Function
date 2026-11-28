import Gauss23RightMesh

/-! The right-side checks for the cells centered at height 24. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell56 : gauss23RightCheck 24 56 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell57 : gauss23RightCheck 24 57 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell58 : gauss23RightCheck 24 58 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell59 : gauss23RightCheck 24 59 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell60 : gauss23RightCheck 24 60 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell61 : gauss23RightCheck 24 61 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell62 : gauss23RightCheck 24 62 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell63 : gauss23RightCheck 24 63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell64 : gauss23RightCheck 24 64 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell65 : gauss23RightCheck 24 65 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell66 : gauss23RightCheck 24 66 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell67 : gauss23RightCheck 24 67 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell68 : gauss23RightCheck 24 68 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell69 : gauss23RightCheck 24 69 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell70 : gauss23RightCheck 24 70 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell71 : gauss23RightCheck 24 71 = true := by
  decide +kernel

theorem gauss23_right_checks_at_24 (j : Fin 16) :
    gauss23RightCheck 24 (56 + j.val) = true := by
  fin_cases j

  · exact checkCell56
  · exact checkCell57
  · exact checkCell58
  · exact checkCell59
  · exact checkCell60
  · exact checkCell61
  · exact checkCell62
  · exact checkCell63
  · exact checkCell64
  · exact checkCell65
  · exact checkCell66
  · exact checkCell67
  · exact checkCell68
  · exact checkCell69
  · exact checkCell70
  · exact checkCell71

#print axioms gauss23_right_checks_at_24

end FieldTarget
