import Discriminant23GaussIntegerComparison
import DedekindDiscriminant23Height29TaylorCertificate

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

theorem discriminant23_height29_ne_zero_of_integer_comparisons
    {trace : Fin 32 → Fin 24 → GaussPanelTrace}
    (hTrace : ∀ (p : Fin 32) (i : Fin 24), (trace p i).approximation = gaussPanelApproximation p.val i)
    (hInteger : ∀ (total : Bool) (k : ℕ), k < 36 → Height29GaussIntegerCheck trace total k)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (29 + 1 / 512) 0) (dottieWeightOuterRadius 0)) :
    mixedThetaContinuation Discriminant23GaloisField w ≠ 0 ∧
    mixedThetaContinuation (discriminant23QuadraticSubfield : Type) w ≠ 0 ∧
    discriminant23CharacterFold w ≠ 0 := by
  apply discriminant23_height29_ne_zero_of_taylor_coefficient_enclosures _ _ hw
  · intro k hk
    simpa [height29GaussCombination] using
      height29TaylorCoeff_enclosure_of_integer_check hTrace (hInteger true k hk)
  · intro k hk
    simpa [height29GaussCombination] using
      height29TaylorCoeff_enclosure_of_integer_check hTrace (hInteger false k hk)

#print axioms discriminant23_height29_ne_zero_of_integer_comparisons

end FieldTarget
