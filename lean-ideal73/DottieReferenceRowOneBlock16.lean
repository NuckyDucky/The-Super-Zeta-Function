import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock16 :
  dottieRowChunk dottieWeightTicks 1 16384 255 = (-536002088062408260937646163915805005001007039116627504101825421295816 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock16

end QuarticModel
