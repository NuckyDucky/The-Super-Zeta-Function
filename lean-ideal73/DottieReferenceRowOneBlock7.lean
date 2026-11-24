import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock7 :
  dottieRowChunk dottieWeightTicks 1 7168 1024 = (-6262731678992288967212056091821868885804590543624667199512095213947776 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock7

end QuarticModel
