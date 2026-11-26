import GaussianVaughanPrimeInversion

/-! The full higher-prime-power reading uses the original two-scale
theta kernel. Removing it before the prime cutoff keeps its cancellation. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory QuarticModel Set

noncomputable section

def archivedGaussianVaughanHigherKernel (v : ℝ) : ℂ :=
  dirichletKernelSum archivedGaussianVaughanHigherCoefficients
    (fun x => (archivedGaussianVaughanKernel x : ℂ)) v

private theorem higherKernel_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt archivedGaussianVaughanHigherKernel v := by
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hL := archivedGaussianVaughanHigher_summable (z := (2 : ℂ)) (by norm_num)
  apply dirichletKernelSum_continuousAt_of_power (s := 2) (by norm_num) hD hv
    (Complex.continuous_ofReal.comp_continuousOn archivedGaussianVaughanKernel_continuousOn) _ hL
  intro x hx
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hK x hx

theorem archivedGaussianVaughanHigherKernel_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin archivedGaussianVaughanHigherKernel z (archivedGaussianVaughanHigherMellin z) := by
  rw [archivedGaussianVaughanHigherMellin_eq hz]
  exact dirichletKernelSum_hasMellin archivedGaussianVaughanHigherCoefficients
    (archivedGaussianVaughanKernel_hasMellin (zero_lt_one.trans hz))
    (archivedGaussianVaughanHigher_summable (by simpa using hz))

private theorem higherMellin_square_decay (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 3 / 2 →
      ‖archivedGaussianVaughanHigherMellin z‖ ≤ C / (1 + |z.im|) ^ (2 : ℕ) := by
  obtain ⟨D, hD, h⟩ := archivedGaussianVaughanHigherMellin_strip hDir
  obtain ⟨B, hB, hTheta⟩ := archivedGaussianThetaMellin_rapid_decay 3
  refine ⟨2 * D * B, by positivity, fun z hl hr => ?_⟩
  let T := 1 + |z.im|
  have hlog : 1 + Real.log (1 + 2 * |z.im|) ≤ 2 * T := by
    dsimp [T]
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 2 * |z.im|)]
  apply (le_div_iff₀ (by positivity : 0 < T ^ (2 : ℕ))).mpr
  calc
    _ ≤ (D * (2 * T) * ‖archivedMellin (z / 7) / 7‖) * T ^ (2 : ℕ) := by
      refine mul_le_mul_of_nonneg_right ((h z hl (by linarith)).trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hD.le) (norm_nonneg _)
    _ = (2 * D) * (T ^ (3 : ℕ) * ‖archivedMellin (z / 7) / 7‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hTheta z hl (by linarith)) (by positivity)

theorem archivedGaussianVaughanHigherKernel_eq_leftMellinInv (hDir : DirichletLZerosOnLine)
    {v : ℝ} (hv : 0 < v) :
    archivedGaussianVaughanHigherKernel v =
      mellinInv (3 / 8) archivedGaussianVaughanHigherMellin v := by
  let K := archivedGaussianVaughanHigherKernel
  let F := archivedGaussianVaughanHigherMellin
  let b : ℝ := 3 / 2
  obtain ⟨C, _, hB⟩ := higherMellin_square_decay hDir
  have hD (z : ℂ) (hl : 3 / 8 ≤ z.re) (_ : z.re ≤ b) : DifferentiableAt ℂ F z :=
    (archivedGaussianVaughanHigherMellin_analyticAt hDir (by linarith)).differentiableAt
  have hR : VerticalIntegrable F b :=
    verticalIntegrable_of_square_decay (by norm_num [b]) le_rfl hD hB
  have hB' : MellinConvergent K (b : ℂ) :=
    (archivedGaussianVaughanHigherKernel_hasMellin (by norm_num [b])).1
  have hby (y : ℝ) : mellin K ((b : ℂ) + (y : ℂ) * I) = F ((b : ℂ) + (y : ℂ) * I) :=
    (archivedGaussianVaughanHigherKernel_hasMellin
      (z := (b : ℂ) + (y : ℂ) * I) (by norm_num [b, mul_re])).2
  have hInv : VerticalIntegrable (mellin K) b := hR.congr (Eventually.of_forall fun y => (hby y).symm)
  calc
    K v = mellinInv b (mellin K) v :=
      (mellinInv_mellin_eq _ _ hv hB' hInv (higherKernel_continuousAt hv)).symm
    _ = mellinInv b F v := by simp only [mellinInv, hby]
    _ = _ := (mellinInv_eq_of_square_decay hv (by norm_num [b]) hD hB).symm

theorem archivedGaussianVaughanHigherKernel_left_powerBound (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ v > (0 : ℝ),
      ‖archivedGaussianVaughanHigherKernel v‖ ≤ C * v ^ (-(3 / 8 : ℝ)) := by
  obtain ⟨D, _, hB⟩ := higherMellin_square_decay hDir
  have hI : VerticalIntegrable archivedGaussianVaughanHigherMellin (3 / 8) :=
    verticalIntegrable_of_square_decay (a := 3 / 8) (b := 3 / 2) le_rfl (by norm_num)
      (fun _ hl _ => (archivedGaussianVaughanHigherMellin_analyticAt hDir (by linarith)).differentiableAt)
      hB
  let C := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖archivedGaussianVaughanHigherMellin (((3 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖
  have hC : 0 ≤ C := mul_nonneg (by positivity [Real.pi_pos]) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨C, hC, fun v hv => ?_⟩
  rw [archivedGaussianVaughanHigherKernel_eq_leftMellinInv hDir hv]
  exact norm_mellinInv_le hv hI

#print axioms archivedGaussianVaughanHigherKernel_hasMellin
#print axioms archivedGaussianVaughanHigherKernel_eq_leftMellinInv
#print axioms archivedGaussianVaughanHigherKernel_left_powerBound

end
end AlpogeSuperZeta
