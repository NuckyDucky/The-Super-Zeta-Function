import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock12 :
  dottieRowChunk dottieWeightTicks 1 12288 1024 = (634872226576407368312468744055450409678860817270561621747856876047896 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock12

end QuarticModel
