import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock6 :
  dottieRowChunk dottieWeightTicks 1 6144 1024 = (-13273388615777028097725703327328370379887368064509214633943252312771952 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock6

end QuarticModel
