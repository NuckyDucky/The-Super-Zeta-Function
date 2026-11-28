import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 13. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell48 :
    (gauss23TwentyCover 48).check (gauss23TwentyValue 13) 48 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell49 :
    (gauss23TwentyCover 49).check (gauss23TwentyValue 13) 49 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell50 :
    (gauss23TwentyCover 50).check (gauss23TwentyValue 13) 50 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell51 :
    (gauss23TwentyCover 51).check (gauss23TwentyValue 13) 51 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell52 :
    (gauss23TwentyCover 52).check (gauss23TwentyValue 13) 52 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell53 :
    (gauss23TwentyCover 53).check (gauss23TwentyValue 13) 53 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell54 :
    (gauss23TwentyCover 54).check (gauss23TwentyValue 13) 54 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell55 :
    (gauss23TwentyCover 55).check (gauss23TwentyValue 13) 55 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell56 :
    (gauss23TwentyCover 56).check (gauss23TwentyValue 13) 56 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell57 :
    (gauss23TwentyCover 57).check (gauss23TwentyValue 13) 57 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell58 :
    (gauss23TwentyCover 58).check (gauss23TwentyValue 13) 58 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell59 :
    (gauss23TwentyCover 59).check (gauss23TwentyValue 13) 59 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell60 :
    (gauss23TwentyCover 60).check (gauss23TwentyValue 13) 60 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell61 :
    (gauss23TwentyCover 61).check (gauss23TwentyValue 13) 61 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell62 :
    (gauss23TwentyCover 62).check (gauss23TwentyValue 13) 62 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell63 :
    (gauss23TwentyCover 63).check (gauss23TwentyValue 13) 63 = true := by
  decide +kernel

theorem gauss23_checks_at_13 (j : Fin 16) :
    (gauss23TwentyCover (48 + j.val)).check (gauss23TwentyValue 13) (48 + j.val) = true := by
  fin_cases j

  · exact checkCell48
  · exact checkCell49
  · exact checkCell50
  · exact checkCell51
  · exact checkCell52
  · exact checkCell53
  · exact checkCell54
  · exact checkCell55
  · exact checkCell56
  · exact checkCell57
  · exact checkCell58
  · exact checkCell59
  · exact checkCell60
  · exact checkCell61
  · exact checkCell62
  · exact checkCell63

#print axioms gauss23_checks_at_13

end FieldTarget
