import ArchivedQuarticZeroTransport
import DerivativeRectangle
import StripCover

/-! Apply the repository's derivative rectangle and all-height cover to
the exact completed factor of the quartic's verified ideal-counting series. -/

open Set Complex
open scoped ComplexConjugate

namespace QuarticModel

open ArtinPrimitiveRootsConjecture FieldCoefficientTransfer

/-- A certified signed remainder bound in the original measuring rectangle
confines the actual Gaussian zeros there to the line. -/
theorem archivedGaussian_dottie_rectangle_of_signed_remainder
    {T margin : ℝ} {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (model : ∀ x ∈ Icc (1/2 : ℝ) (1/2+63/2048),
      ∀ t ∈ Icc (T-35/2048) (T+27/2048),
        (deriv H (GaussianRectangle.point x t)).im < -margin)
    (tail : ∀ x ∈ Icc (1/2 : ℝ) (1/2+63/2048),
      ∀ t ∈ Icc (T-35/2048) (T+27/2048),
        (deriv (fun w => archivedMellin w - H w) (GaussianRectangle.point x t)).im ≤ margin)
    {x t : ℝ} (hx : x ∈ Icc (1/2 : ℝ) (1/2+63/2048))
    (ht : t ∈ Icc (T-35/2048) (T+27/2048))
    (hz : archivedGaussianFactor (GaussianRectangle.point x t) = 0) :
    x = 1/2 := by
  let R := fun w => archivedMellin w - H w
  have hR : Differentiable ℂ R := (archivedMellin_differentiable archivedTheta_reflection).sub hH
  have hsum (w : ℂ) : H w + (archivedMellin w - H w) = archivedMellin w := by abel
  have hr : 0 < (GaussianRectangle.point x t).re := by
    have hx0 := hx.1
    simp [GaussianRectangle.point]
    linarith
  have hz' := (archivedGaussianFactor_zero_iff_mellin hr).mp hz
  refine GaussianRectangle.zero_on_line_of_remainder (P := H) (R := R)
    (DP := deriv H) (DR := deriv R) (margin := margin) (by constructor <;> norm_num)
    ?_ (fun y _ s _ => (hH _).hasDerivAt) (fun y _ s _ => (hR _).hasDerivAt)
    model tail hx ht ?_
  · intro s _
    change (H _ + (archivedMellin _ - H _)).im = 0
    rw [hsum]
    exact GaussianRectangle.real_on_line_of_reflection archivedMellin_mirror s
  · change H _ + (archivedMellin _ - H _) = 0
    rwa [hsum]

theorem archivedGaussian_strip_iff_boxMargins :
    FieldTarget.StripZerosOnLine archivedGaussianFactor ↔ StripCover.BoxMargins archivedMellin := by
  have heq : FieldTarget.StripZerosOnLine archivedGaussianFactor ↔
      FieldTarget.StripZerosOnLine archivedMellin := by
    constructor
    · intro h w h₀ h₁ hz
      exact h w h₀ h₁ ((archivedGaussianFactor_zero_iff_mellin h₀).mpr hz)
    · intro h w h₀ h₁ hz
      exact h w h₀ h₁ ((archivedGaussianFactor_zero_iff_mellin h₀).mp hz)
  refine heq.trans (StripCover.strip_iff_boxMargins
    (fun _ => (archivedMellin_differentiable archivedTheta_reflection).continuous.continuousOn) ?_)
  intro w _ _ hz
  have hmirror : StripCover.reflection w = 1-conj w := by
    apply Complex.ext <;> simp [StripCover.reflection]
  rw [hmirror, archivedMellin_mirror, hz, map_zero]

/-- The exact field claim decomposes into the two rational input claims and
the repository's compact-cover test on the completed Gaussian factor. -/
theorem archivedQuarticRH_iff_boxMargins :
    DedekindZetaRH K ↔ FieldTarget.StripZerosOnLine riemannZeta ∧
      FieldTarget.StripZerosOnLine chi4.LFunction ∧ StripCover.BoxMargins archivedMellin := by
  rw [archivedQuarticRH_iff_three_factors, archivedGaussian_strip_iff_boxMargins]

#print axioms archivedGaussian_dottie_rectangle_of_signed_remainder
#print axioms archivedQuarticRH_iff_boxMargins

end QuarticModel
