import DottieCayleySamplePolynomial
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

theorem dottieCayleyCauchyMajorant :
    ∀ w ∈ sphere dottieCayleyCenter (1 / 2 : ℝ), ‖riemannZeta w‖ ≤ 10 ^ 9 :=
  dottieCayleyCauchyMajorant_of_growth Formalism.ZF.growthBound

/-- The signed arc test for ordinary zeta itself. The uniform approximation
budget follows from the 96 sample enclosures and the proved Cauchy majorant. -/
theorem dottieCayley_riemannZeta_ne_zero_of_96_samples {m : ℕ} (hm : 0 < m)
    (samples : ℕ → ℂ)
    (hSample : ∀ j < 96, ‖samples j - riemannZeta (dottieCayleySamplePoint j)‖ ≤ 1 / 10 ^ 12)
    (hArcs : ∀ a ∈ contourQuarterTurns, ∀ j : Fin m, ∀ t ∈
      Icc (((j : ℕ) : ℝ) / m) ((((j : ℕ) : ℝ) + 1) / m),
      let w := rationalContourPoint dottieCayleyCenter (31 / 128) a t
      (dottieCayleyZetaPolynomial samples w).im + 1 / 10 ^ 9 ≤ -(1 / 16)) :
    ∀ w ∈ closedBall dottieCayleyCenter (31 / 128 : ℝ), riemannZeta w ≠ 0 := by
  apply dottieCayley_riemannZeta_ne_zero_of_sample_polynomial (W := fun _ => 1)
    (differentiableOn_const _) hm samples dottieCayleyCauchyMajorant hSample
  simpa only [norm_one, one_mul] using hArcs

#print axioms Formalism.ZF.growthBound
#print axioms dottieCayleyCauchyMajorant
#check @dottieCayley_riemannZeta_ne_zero_of_96_samples
#print axioms dottieCayley_riemannZeta_ne_zero_of_96_samples

end FieldTarget
