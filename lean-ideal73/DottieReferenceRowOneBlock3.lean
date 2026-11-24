import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock3 :
  dottieRowChunk dottieWeightTicks 1 3072 1024 = (9478745443266999068150930465822810140803767061037670413745277359970888 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock3

end QuarticModel
