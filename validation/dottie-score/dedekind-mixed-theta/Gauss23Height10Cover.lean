import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 10. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell0 :
    (gauss23TwentyCover 0).check (gauss23TwentyValue 10) 0 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell1 :
    (gauss23TwentyCover 1).check (gauss23TwentyValue 10) 1 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell2 :
    (gauss23TwentyCover 2).check (gauss23TwentyValue 10) 2 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell3 :
    (gauss23TwentyCover 3).check (gauss23TwentyValue 10) 3 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell4 :
    (gauss23TwentyCover 4).check (gauss23TwentyValue 10) 4 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell5 :
    (gauss23TwentyCover 5).check (gauss23TwentyValue 10) 5 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell6 :
    (gauss23TwentyCover 6).check (gauss23TwentyValue 10) 6 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell7 :
    (gauss23TwentyCover 7).check (gauss23TwentyValue 10) 7 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell8 :
    (gauss23TwentyCover 8).check (gauss23TwentyValue 10) 8 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell9 :
    (gauss23TwentyCover 9).check (gauss23TwentyValue 10) 9 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell10 :
    (gauss23TwentyCover 10).check (gauss23TwentyValue 10) 10 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell11 :
    (gauss23TwentyCover 11).check (gauss23TwentyValue 10) 11 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell12 :
    (gauss23TwentyCover 12).check (gauss23TwentyValue 10) 12 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell13 :
    (gauss23TwentyCover 13).check (gauss23TwentyValue 10) 13 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell14 :
    (gauss23TwentyCover 14).check (gauss23TwentyValue 10) 14 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell15 :
    (gauss23TwentyCover 15).check (gauss23TwentyValue 10) 15 = true := by
  decide +kernel

theorem gauss23_checks_at_10 (j : Fin 16) :
    (gauss23TwentyCover (0 + j.val)).check (gauss23TwentyValue 10) (0 + j.val) = true := by
  fin_cases j

  · exact checkCell0
  · exact checkCell1
  · exact checkCell2
  · exact checkCell3
  · exact checkCell4
  · exact checkCell5
  · exact checkCell6
  · exact checkCell7
  · exact checkCell8
  · exact checkCell9
  · exact checkCell10
  · exact checkCell11
  · exact checkCell12
  · exact checkCell13
  · exact checkCell14
  · exact checkCell15

#print axioms gauss23_checks_at_10

end FieldTarget
