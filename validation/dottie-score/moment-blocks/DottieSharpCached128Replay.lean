import DottieFastSharpWeights
import DottieJointSharpChunk0

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

theorem dottie_sharp_cached_128_ticks :
    dottieFastJointMomentBlock 11 26858 0 128
      0x69408041c9001021209045124824a34d209291189089242288241281050250c8004822a48944024209204a2022083810 = dottieSharpChunk0Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_128_ticks

end QuarticModel.DottieFixedIntervals
