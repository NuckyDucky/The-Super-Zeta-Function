import GaussianPrimeOnlyWindow
import ArchivedGaussianHalfMellin
import QuarticRealFormula

/-! Detect Gaussian poles using a lower bound on the archived prime sum.
The sign reversal uses nonvanishing on the positive real axis. -/

open scoped Topology

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture

noncomputable section

private theorem negate_pole_data {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : Deduction.PoleData g Φ Z) (hreal : ∀ ρ ∈ Z, ρ.im ≠ 0) :
    Deduction.PoleData (fun u => -g u) (fun w => -Φ w) Z := by
  refine ⟨hP.meas.neg, ?_, ?_, hP.pos, hP.diff.neg, hP.iso, ?_⟩
  · simpa only [abs_neg] using hP.growth
  · intro w hw
    simp only [Complex.ofReal_neg, neg_mul, integral_neg]
    simpa only [neg_mul] using congrArg (fun z : ℂ => -z) (hP.laplace w hw)
  · intro ρ hρ
    obtain ⟨c, hc, _, a, ha, he⟩ := hP.pole ρ hρ
    refine ⟨-c, neg_ne_zero.mpr hc, fun h => (hreal ρ hρ h).elim,
      fun w => -a w, ha.neg, ?_⟩
    filter_upwards [he] with w hw
    rw [hw, neg_add, neg_div]

theorem gaussian_poles_nonreal_of_mellin_pos
    (hpos : ∀ σ : ℝ, 0 < σ → 0 < (archivedMellin (σ : ℂ)).re) :
    ∀ ρ ∈ gaussianPoles, ρ.im ≠ 0 := by
  intro ρ hρ hi
  have hρre : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simpa using hi.symm)
  have hM := (archivedGaussianFactor_zero_iff_mellin hρ.1).mp hρ.2
  exact (hpos ρ.re hρ.1).ne' (by rw [hρre, hM, Complex.zero_re])

/-- A lower bound for the same corrected prime-only ramp on cofinal windows. -/
def ArchivedGaussianPrimeOnlyLowerWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Icc Y (Y ^ (1 + δ)), -archivedGaussianPrimeOnlyRamp y ≤ C * y ^ θ

/-- The lower bound suffices once the real Gaussian zeros have been excluded. -/
theorem quartic_rh_of_archived_gaussian_prime_only_lower_windows
    (hD : DirichletLZerosOnLine) (hreal : ∀ ρ ∈ gaussianPoles, ρ.im ≠ 0)
    (hcut : ArchivedGaussianPrimeOnlyLowerWindowBound) : DedekindZetaRH QuarticModel.K := by
  let a := archivedGaussianPrimeWeight
  let g := gaussianLogCutoffRamp a
  have hLap (w : ℂ) (hw : 2 < w.re) :
      gaussianPoleFormula w = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * exp (-w * u) :=
    gaussianLogCutoffRamp_laplace a archivedGaussianPrimeWeight_abs_le_two hw
      (archivedGaussianMangoldt_eq_neg_logDeriv (by linarith))
  obtain ⟨Φ, hP⟩ := gaussian_pole_data_of_laplace g (gaussianLogCutoffRamp_measurable a)
    (gaussianLogCutoffRamp_growth a archivedGaussianPrimeWeight_abs_le_two) hLap
    gaussian_real_poles_lt_one
  apply quartic_rh_of_gaussian_windows hD (negate_pole_data hP hreal)
  intro θ hθ₀ hθ₁
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ hθ₀ hθ₁
  obtain ⟨D, hD₀, hE⟩ := archivedGaussianPrimeOnlyRamp_error hθ₀ hθ₁.le
  refine ⟨δ, hδ, logWindow_of_pointwise_norm_windows
    (fun y => -gaussianPrimeNormRamp a y) hδ (add_nonneg hC hD₀) ?_⟩
  intro Y₀
  obtain ⟨Y, hY, hB⟩ := hW (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) ≤ y := (le_max_right Y₀ (1 : ℝ)).trans (hY.trans hy.1)
  rw [add_mul]
  dsimp only [a]
  linarith [(abs_le.mp (hE y h1)).1, hB y hy]

theorem quartic_rh_of_archived_gaussian_prime_only_lower_windows_of_mellin_pos
    (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < σ → 0 < (archivedMellin (σ : ℂ)).re)
    (hcut : ArchivedGaussianPrimeOnlyLowerWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_prime_only_lower_windows hD
    (gaussian_poles_nonreal_of_mellin_pos hpos) hcut

/-- The explicit formula used by the prefix certificate is the field's
actual Mellin transform. -/
theorem archivedMellin_eq_quartic_real_formula :
    archivedMellin = QuarticRealFormula.completed := by
  funext w
  unfold archivedMellin QuarticRealFormula.completed mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hu : 0 < t / archivedThetaScale := div_pos ht archivedThetaScale_pos
  have htheta : archivedTheta (t / archivedThetaScale) =
      QuarticRealFormula.theta (t / archivedThetaScale) := by
    simpa only [QuarticRealFormula.theta, jacobiSym.legendreSym.to_jacobiSym] using
      archivedTheta_eq_original_quarter hu
  exact congrArg (fun v : ℝ => (t : ℂ) ^ (w - 1) • (v : ℂ)) htheta

theorem quartic_rh_of_lower_windows_and_real_positivity (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ArchivedGaussianPrimeOnlyLowerWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_prime_only_lower_windows_of_mellin_pos hD
    (fun σ _ => archivedMellin_eq_quartic_real_formula ▸ hpos σ) hcut

#check quartic_rh_of_lower_windows_and_real_positivity
#print ArchivedGaussianPrimeOnlyLowerWindowBound
#print axioms negate_pole_data
#print axioms gaussian_poles_nonreal_of_mellin_pos
#print axioms quartic_rh_of_archived_gaussian_prime_only_lower_windows
#print axioms quartic_rh_of_archived_gaussian_prime_only_lower_windows_of_mellin_pos
#print axioms archivedMellin_eq_quartic_real_formula
#print axioms quartic_rh_of_lower_windows_and_real_positivity

end
end AlpogeSuperZeta
