import DottieRetainedLongBandJoin
import DottieLongBand1Assembly

namespace QuarticModel

/-- The complete first retained band, including its adjacent short block. -/
theorem dottie_retained_quarter_integer_sums :
    DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12 :=
  dottie_retained_quarter_bounds_of_long_chunk DottieLongBand1Assembly.certificate

#print axioms dottie_retained_quarter_integer_sums

end QuarticModel
