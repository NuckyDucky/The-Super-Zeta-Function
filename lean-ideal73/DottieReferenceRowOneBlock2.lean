import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock2 :
  dottieRowChunk dottieWeightTicks 1 2048 1024 = (33862694293993958250633048373076417567780343046513865869995826984462184 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock2

end QuarticModel
