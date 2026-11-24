import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock11 :
  dottieRowChunk dottieWeightTicks 1 11264 1024 = (1205819299184500382976842277401446985958480865169802226817191271839488 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock11

end QuarticModel
