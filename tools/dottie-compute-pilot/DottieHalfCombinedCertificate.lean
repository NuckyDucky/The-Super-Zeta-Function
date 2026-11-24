import DottieRetainedLongBandJoin
import DottieLongBand2Assembly

namespace QuarticModel

/-- The complete second retained band, including its adjacent short block. -/
theorem dottie_retained_half_integer_sums :
    DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482 :=
  dottie_retained_half_bounds_of_long_chunk DottieLongBand2Assembly.certificate

#print axioms dottie_retained_half_integer_sums

end QuarticModel
