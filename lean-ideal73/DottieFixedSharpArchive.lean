import DottieFixedSharpModel
import DottieFixedSharpData

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection

/-- The exact circle calculation, conditional on the retained low-degree
moment rectangles. The other coefficients use the absolute mass bound. -/
theorem dottie_sharp_margin_of_fixed_archive_moments
    (hSharp : ∀ k < 11, (fixedSharpInput k).Contains
      (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k))
    (hRef : ∀ k < 6, (fixedReferenceInput k).Contains
      (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply sharp_margin_of_fixed_moment_rectangles _ _ _ fixedCheckedArcs_cover fixedCheckedArcs_scalar fixedCheckedArcs_pass
  · intro k _
    by_cases h : k < 11
    · exact hSharp k h
    · simpa only [fixedSharpInput,if_neg h] using sharpTailMomentBox_sound k
  · intro k _
    by_cases h : k < 6
    · exact hRef k h
    · simpa only [fixedReferenceInput,if_neg h] using referenceTailMomentBox_sound k

#print axioms dottie_sharp_margin_of_fixed_archive_moments

end QuarticModel.DottieFixedIntervals
