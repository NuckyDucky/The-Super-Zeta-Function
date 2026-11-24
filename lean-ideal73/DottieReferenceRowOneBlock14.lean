import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock14 :
  dottieRowChunk dottieWeightTicks 1 14336 1024 = (1480760986469248524099590652957144781628096621920003717307442580176936 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock14

end QuarticModel
