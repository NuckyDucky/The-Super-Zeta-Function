import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 11. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell16 :
    (gauss23TwentyCover 16).check (gauss23TwentyValue 11) 16 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell17 :
    (gauss23TwentyCover 17).check (gauss23TwentyValue 11) 17 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell18 :
    (gauss23TwentyCover 18).check (gauss23TwentyValue 11) 18 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell19 :
    (gauss23TwentyCover 19).check (gauss23TwentyValue 11) 19 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell20 :
    (gauss23TwentyCover 20).check (gauss23TwentyValue 11) 20 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell21 :
    (gauss23TwentyCover 21).check (gauss23TwentyValue 11) 21 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell22 :
    (gauss23TwentyCover 22).check (gauss23TwentyValue 11) 22 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell23 :
    (gauss23TwentyCover 23).check (gauss23TwentyValue 11) 23 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell24 :
    (gauss23TwentyCover 24).check (gauss23TwentyValue 11) 24 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell25 :
    (gauss23TwentyCover 25).check (gauss23TwentyValue 11) 25 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell26 :
    (gauss23TwentyCover 26).check (gauss23TwentyValue 11) 26 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell27 :
    (gauss23TwentyCover 27).check (gauss23TwentyValue 11) 27 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell28 :
    (gauss23TwentyCover 28).check (gauss23TwentyValue 11) 28 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell29 :
    (gauss23TwentyCover 29).check (gauss23TwentyValue 11) 29 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell30 :
    (gauss23TwentyCover 30).check (gauss23TwentyValue 11) 30 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell31 :
    (gauss23TwentyCover 31).check (gauss23TwentyValue 11) 31 = true := by
  decide +kernel

theorem gauss23_checks_at_11 (j : Fin 16) :
    (gauss23TwentyCover (16 + j.val)).check (gauss23TwentyValue 11) (16 + j.val) = true := by
  fin_cases j

  · exact checkCell16
  · exact checkCell17
  · exact checkCell18
  · exact checkCell19
  · exact checkCell20
  · exact checkCell21
  · exact checkCell22
  · exact checkCell23
  · exact checkCell24
  · exact checkCell25
  · exact checkCell26
  · exact checkCell27
  · exact checkCell28
  · exact checkCell29
  · exact checkCell30
  · exact checkCell31

#print axioms gauss23_checks_at_11

end FieldTarget
