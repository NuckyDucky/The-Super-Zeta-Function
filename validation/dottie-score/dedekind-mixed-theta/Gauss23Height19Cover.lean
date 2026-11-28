import Gauss23TwentyGrid
import Gauss23TwentyValues

/-! The signed rectangle arithmetic for the cells centered at height 19. -/

namespace FieldTarget

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell144 :
    (gauss23TwentyCover 144).check (gauss23TwentyValue 19) 144 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell145 :
    (gauss23TwentyCover 145).check (gauss23TwentyValue 19) 145 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell146 :
    (gauss23TwentyCover 146).check (gauss23TwentyValue 19) 146 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell147 :
    (gauss23TwentyCover 147).check (gauss23TwentyValue 19) 147 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell148 :
    (gauss23TwentyCover 148).check (gauss23TwentyValue 19) 148 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell149 :
    (gauss23TwentyCover 149).check (gauss23TwentyValue 19) 149 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell150 :
    (gauss23TwentyCover 150).check (gauss23TwentyValue 19) 150 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell151 :
    (gauss23TwentyCover 151).check (gauss23TwentyValue 19) 151 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell152 :
    (gauss23TwentyCover 152).check (gauss23TwentyValue 19) 152 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell153 :
    (gauss23TwentyCover 153).check (gauss23TwentyValue 19) 153 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell154 :
    (gauss23TwentyCover 154).check (gauss23TwentyValue 19) 154 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell155 :
    (gauss23TwentyCover 155).check (gauss23TwentyValue 19) 155 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell156 :
    (gauss23TwentyCover 156).check (gauss23TwentyValue 19) 156 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell157 :
    (gauss23TwentyCover 157).check (gauss23TwentyValue 19) 157 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell158 :
    (gauss23TwentyCover 158).check (gauss23TwentyValue 19) 158 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem checkCell159 :
    (gauss23TwentyCover 159).check (gauss23TwentyValue 19) 159 = true := by
  decide +kernel

theorem gauss23_checks_at_19 (j : Fin 16) :
    (gauss23TwentyCover (144 + j.val)).check (gauss23TwentyValue 19) (144 + j.val) = true := by
  fin_cases j

  · exact checkCell144
  · exact checkCell145
  · exact checkCell146
  · exact checkCell147
  · exact checkCell148
  · exact checkCell149
  · exact checkCell150
  · exact checkCell151
  · exact checkCell152
  · exact checkCell153
  · exact checkCell154
  · exact checkCell155
  · exact checkCell156
  · exact checkCell157
  · exact checkCell158
  · exact checkCell159

#print axioms gauss23_checks_at_19

end FieldTarget
