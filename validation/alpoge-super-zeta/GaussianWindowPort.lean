import GaussianPolePort
import ArchivedQuarticZeroTransport
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow

namespace AlpogeSuperZeta

open Complex Set Filter MeasureTheory SuperZeta QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Topology

noncomputable section

/-- The exact window condition for the Gaussian arithmetic sum, in the
logarithmic cutoff variable rather than in the ordinate of a trial point. -/
def GaussianWindows (g : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ > 0, Deduction.WindowHypU g θ δ

/-- Bring the full upstream window implication through the archived
Gaussian reading and the exact field reduction. -/
theorem quartic_rh_of_gaussian_windows (hD : DirichletLZerosOnLine)
    {g : ℝ → ℝ} {Φ : ℂ → ℂ} (hP : Deduction.PoleData g Φ gaussianPoles)
    (hW : GaussianWindows g) : DedekindZetaRH QuarticModel.K := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hD
  apply archivedQuarticRH_iff_upper_right.mpr
  refine ⟨hR, hB, ?_⟩
  intro w hright hleft _ hz
  have hpos : 0 < w.re := by linarith
  have hw : w ∈ gaussianPoles := ⟨hpos, (archivedGaussianFactor_zero_iff_mellin hpos).mpr hz⟩
  let θ : ℝ := (1 / 2 + w.re) / 2
  have ht₀ : 1 / 2 < θ := by dsimp [θ]; linarith
  have ht₁ : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨δ, hδ, hwindow⟩ := hW θ ht₀ ht₁
  have hcut := Deduction.landau_window hP (by linarith : 0 < θ) ht₁ hδ hwindow w hw
  dsimp [θ] at hcut
  linarith

/-- This signature exposes each open analytic input needed from the actual
Gaussian ramp, independently of the finite Dottie-ring arithmetic. -/
theorem quartic_rh_of_gaussian_ramp (hD : DirichletLZerosOnLine)
    (g : ℝ → ℝ) (hMeas : Measurable g)
    (hGrowth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (hLaplace : ∀ w : ℂ, 2 < w.re →
      gaussianPoleFormula w = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * exp (-w * u))
    (hReal : ∀ ρ ∈ gaussianPoles, ρ.im = 0 → ρ.re < 1)
    (hWindows : GaussianWindows g) : DedekindZetaRH QuarticModel.K := by
  obtain ⟨_, hP⟩ := gaussian_pole_data_of_laplace g hMeas hGrowth hLaplace hReal
  exact quartic_rh_of_gaussian_windows hD hP hWindows

#check @Deduction.landau_window
#print GaussianWindows
#check @quartic_rh_of_gaussian_ramp
#print axioms Deduction.landau_window
#print axioms quartic_rh_of_gaussian_windows
#print axioms quartic_rh_of_gaussian_ramp

end
end AlpogeSuperZeta
