import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock5 :
  dottieRowChunk dottieWeightTicks 1 5120 1024 = (-8645569771031968819636257576990413175380081221147423532271776899229024 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock5

end QuarticModel
