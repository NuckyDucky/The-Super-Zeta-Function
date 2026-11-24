import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock9 :
  dottieRowChunk dottieWeightTicks 1 9216 1024 = (-7474247192534191938020449492312701769620009465786242665939135478751416 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock9

end QuarticModel
