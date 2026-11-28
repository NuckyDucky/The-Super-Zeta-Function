import Height29IntegerTrace.CoefficientsChecked
import Height29IntegerTrace.TraceChecked
import Discriminant23Height29IntegerTransfer

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

theorem discriminant23_height29_ne_zero_kernel
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (29 + 1 / 512) 0) (dottieWeightOuterRadius 0)) :
    mixedThetaContinuation Discriminant23GaloisField w ≠ 0 ∧
    mixedThetaContinuation (discriminant23QuadraticSubfield : Type) w ≠ 0 ∧
    discriminant23CharacterFold w ≠ 0 :=
  discriminant23_height29_ne_zero_of_integer_comparisons height29_gauss_trace_approximations
    height29_gauss_integer_coefficients_checked hw

#check @discriminant23_height29_ne_zero_kernel
#print axioms discriminant23_height29_ne_zero_kernel

end FieldTarget
