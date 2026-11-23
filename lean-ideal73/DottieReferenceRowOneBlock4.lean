import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock4 :
  dottieRowChunk dottieWeightTicks 1 4096 1024 = (-4883933133356808275043562215574363417337057783557292109704407963657504 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock4

end QuarticModel
