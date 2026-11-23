import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock8 :
  dottieRowChunk dottieWeightTicks 1 8192 1024 = (5705545325711542214417572158328192861088596310103550302872554268617760 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock8

end QuarticModel
