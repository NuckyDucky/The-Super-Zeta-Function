import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock1 :
  dottieRowChunk dottieWeightTicks 1 1024 1024 = (2500550436732004101838504610831312600054591718463146698759204838272648 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock1

end QuarticModel
