import GaussianVaughanConvolvedStrip
import GaussianVaughanSelectedContour
import GaussianVaughanPrimeInversion

/-! Shift the inverse of the actual convolved kernel to the selected
negative line. This proves the small-argument estimate for the kernel. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory QuarticModel Set

noncomputable section

private abbrev convolvedKernel (v : ℝ) : ℂ := archivedGaussianVaughanConvolvedKernel v

theorem archivedGaussianVaughanConvolvedKernel_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt convolvedKernel v := by
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  let H (x : ℝ) : ℂ := archivedGaussianVaughanKernel x
  have hEq : convolvedKernel = dirichletKernelSum signedIdealCoefficients H := by
    funext x
    show (archivedGaussianVaughanConvolvedKernel x : ℂ) =
      dirichletKernelSum signedIdealCoefficients H x
    unfold archivedGaussianVaughanConvolvedKernel dirichletKernelSum
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [H, signedIdealCoefficients_eq_archivedLatticeCoeff, ofReal_mul, intCast_re,
      ofReal_intCast]
  rw [hEq]
  have hL := (archivedGaussianFactor_hasSum (w := ((2 : ℝ) : ℂ)) (by norm_num)).LSeriesSummable
  apply dirichletKernelSum_continuousAt_of_power (s := 2) (by norm_num) hD hv
    (Complex.continuous_ofReal.comp_continuousOn archivedGaussianVaughanKernel_continuousOn) _ hL
  intro x hx
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hK x hx

theorem archivedGaussianVaughanConvolvedKernel_eq_leftMellinInv (N : ℕ)
    {v : ℝ} (hv : 0 < v) :
    (archivedGaussianVaughanConvolvedKernel v : ℂ) =
      mellinInv (-((7 * N : ℕ) : ℝ)) archivedGaussianVaughanConvolvedMellin v := by
  let a : ℝ := -((7 * N : ℕ) : ℝ)
  let b : ℝ := 3 / 2
  let F := archivedGaussianVaughanConvolvedMellin
  obtain ⟨C, _, hB⟩ := archivedGaussianVaughanConvolvedMellin_square_decay N
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [Nat.cast_nonneg (α := ℝ) (7 * N)]
  have hD (z : ℂ) (_ : a ≤ z.re) (_ : z.re ≤ b) : DifferentiableAt ℂ F z :=
    archivedGaussianVaughanConvolvedMellin_entire z
  have hRight : VerticalIntegrable F b :=
    verticalIntegrable_of_square_decay hab le_rfl hD hB
  have hConverges : MellinConvergent convolvedKernel (b : ℂ) :=
    (archivedGaussianVaughanConvolvedKernel_hasMellin (z := (b : ℂ)) (by norm_num [b])).1
  have hRead (t : ℝ) : mellin convolvedKernel ((b : ℂ) + (t : ℂ) * I) =
      F ((b : ℂ) + (t : ℂ) * I) :=
    (archivedGaussianVaughanConvolvedKernel_hasMellin
      (by simp [b, mul_re]; norm_num)).2
  have hInvInt : VerticalIntegrable (mellin convolvedKernel) b :=
    hRight.congr (Eventually.of_forall fun t => (hRead t).symm)
  calc
    convolvedKernel v = mellinInv b (mellin convolvedKernel) v :=
      (mellinInv_mellin_eq b convolvedKernel hv hConverges hInvInt
        (archivedGaussianVaughanConvolvedKernel_continuousAt hv)).symm
    _ = mellinInv b F v := by simp only [mellinInv, hRead]
    _ = _ := (mellinInv_eq_of_square_decay hv hab hD hB).symm

theorem archivedGaussianVaughanConvolvedKernel_small_argument :
    ∃ C > 0, ∃ c > 0, ∃ v₀ > 0, ∀ v > 0, v ≤ v₀ →
      |archivedGaussianVaughanConvolvedKernel v| ≤ C * Real.exp (-c * v ^ (-(7 / 15 : ℝ))) := by
  obtain ⟨C, hC, c, hc, v₀, hv₀, hBound⟩ :=
    archivedGaussianVaughanConvolvedMellin_selected_inverse_bound
  refine ⟨C, hC, c, hc, v₀, hv₀, fun v hv hvle => ?_⟩
  obtain ⟨N, _, h⟩ := hBound v hv hvle
  rw [← archivedGaussianVaughanConvolvedKernel_eq_leftMellinInv N hv, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

#check archivedGaussianVaughanConvolvedKernel_small_argument
#print axioms archivedGaussianVaughanConvolvedKernel_continuousAt
#print axioms archivedGaussianVaughanConvolvedKernel_eq_leftMellinInv
#print axioms archivedGaussianVaughanConvolvedKernel_small_argument

end
end AlpogeSuperZeta
