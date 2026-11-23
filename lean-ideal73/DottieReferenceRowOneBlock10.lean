import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieRowOneBlock10 :
  dottieRowChunk dottieWeightTicks 1 10240 1024 = (2444519394771801347613905840310121815237567284283743512468062145583720 : ℤ) := by
  decide +kernel

#print axioms dottieRowOneBlock10

end QuarticModel
