import DottieScoreChunks

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieFirstReferenceBlock :
    dottieRowChunk dottieWeightTicks 1 0 1024 = (-595669624096953086499673633335157321684309854535465688946010176679818760 : ℤ) := by
  decide +kernel

#print axioms dottieFirstReferenceBlock

end QuarticModel
