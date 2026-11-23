import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock15 :
  dottieRowChunk dottieWeightTicks 1 15360 1024 = (2592274659876795443548817619077608825857206420761516778264401196244312 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock15

end QuarticModel
