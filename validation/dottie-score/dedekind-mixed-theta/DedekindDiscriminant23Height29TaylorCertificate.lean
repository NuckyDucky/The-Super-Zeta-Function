import DedekindDiscriminant23Height29TaylorTransfer
import DedekindDiscriminant23Height29TaylorArithmetic

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

noncomputable section

local notation "c29" => discriminant23Height29TaylorCenter

/-- The 72 coefficient enclosures are sufficient for the original disk.
The phase and polynomial comparisons have been checked in the kernel. -/
theorem discriminant23_height29_ne_zero_of_taylor_coefficient_enclosures
    (hBase : ∀ k < 36, ‖discriminant23ClassCombinationTaylorCoeff 2 c29 k -
      discriminant23Height29TaylorApprox true k‖ ≤ 1 / 10 ^ 27)
    (hHecke : ∀ k < 36, ‖discriminant23ClassCombinationTaylorCoeff (-1) c29 k -
      discriminant23Height29TaylorApprox false k‖ ≤ 1 / 10 ^ 27)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (29 + 1 / 512) 0) (dottieWeightOuterRadius 0)) :
    mixedThetaContinuation Discriminant23GaloisField w ≠ 0 ∧
    mixedThetaContinuation (discriminant23QuadraticSubfield : Type) w ≠ 0 ∧
    discriminant23CharacterFold w ≠ 0 :=
  discriminant23_height29_ne_zero_of_quadrature_enclosures
    (fun j hj ↦ discriminant23_height29_base_quadrature_of_taylor hBase hj (height29TaylorComparisons ⟨j, hj⟩))
    (fun j hj ↦ discriminant23_height29_hecke_quadrature_of_taylor hHecke hj (height29TaylorComparisons ⟨j, hj⟩))
    hw

#check @discriminant23_height29_ne_zero_of_taylor_coefficient_enclosures
#print axioms discriminant23_height29_ne_zero_of_taylor_coefficient_enclosures

end
end FieldTarget
