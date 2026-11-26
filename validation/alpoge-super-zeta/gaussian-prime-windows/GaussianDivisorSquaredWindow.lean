import GaussianSquaredRamp
import GaussianRawWindowCriterion

/-! The squared full-prefix cutoff preserves the Gaussian poles used
in the one-sided window criterion for the archived quartic. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture

noncomputable section

def archivedGaussianSquaredWindow : ℝ → ℝ :=
  indexedSquaredRamp (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
    (divisorWindowIndex gaussianIndexAddress)

theorem archivedGaussianSquaredWindow_eq_sum {x : ℝ} (hx : 1 ≤ x) :
    archivedGaussianSquaredWindow x =
      ∑' p : GaussianIndexFamily × ℕ, gaussianIndexCoefficient p.1 *
        squaredRampWeight x (divisorWindowIndex gaussianIndexAddress p) :=
  indexedSquaredRamp_eq_sum _ _ (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (a := 2) (by norm_num) hx
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress (by norm_num)
      (gaussianIndexFamily_summable (by norm_num)))

theorem archivedGaussianSquaredWindow_growth :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |archivedGaussianSquaredWindow x| ≤ C * x ^ (2 : ℝ) := by
  let T := ∑' p : GaussianIndexFamily × ℕ, |gaussianIndexCoefficient p.1| /
    (divisorWindowIndex gaussianIndexAddress p : ℝ) ^ (2 : ℝ)
  refine ⟨T, tsum_nonneg (fun _ => by positivity), fun x hx => ?_⟩
  rw [mul_comm T]
  exact indexedSquaredRamp_abs_le _ _ (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (a := 2) (by norm_num) hx
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress (by norm_num)
      (gaussianIndexFamily_summable (by norm_num)))

private theorem squaredWindowDenominator_ne_zero {w : ℂ} (hw : 0 < w.re) :
    (w + 1) * (w + 2) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    change w.re + (1 : ℝ) = 0 at hr
    linarith
  · intro h
    have hr := congrArg Complex.re h
    change w.re + (2 : ℝ) = 0 at hr
    linarith

theorem archivedGaussianSquaredWindow_mellin {w : ℂ} (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), (archivedGaussianSquaredWindow x : ℂ) * (x : ℂ) ^ (-w - 1) =
      (2 / ((w + 1) * (w + 2))) * ((w - 1) * riemannZeta w) *
        (archivedGaussianPrimitiveIndexMellin w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w) := by
  unfold archivedGaussianSquaredWindow
  rw [(indexedSquaredRamp_mellin _ _ (divisorWindowIndex_pos gaussianIndexAddress_pos) hw
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress hw
      (gaussianIndexFamily_summable hw))).2, archivedGaussianDivisorSeries hw]
  have h0 := (Deduction.mellin_Gchi_of_ne_one_ne hw).1
  have hden := squaredWindowDenominator_ne_zero (one_pos.trans hw)
  field_simp

theorem quartic_rh_of_archived_gaussian_prefix_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianRawPrefix) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_gaussian_cutoff_windows hD hpos (M := fun _ => 1)
    archivedGaussianRawPrefix_measurable archivedGaussianRawPrefix_growth (fun _ _ => analyticAt_const)
    (fun _ _ => one_ne_zero) (fun _ hw => by
      simpa only [one_mul] using archivedGaussianRawPrefix_mellin hw) hcut

theorem quartic_rh_of_archived_gaussian_squared_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianSquaredWindow) : DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_gaussian_cutoff_windows hD hpos
    (A := archivedGaussianSquaredWindow) (M := fun w => 2 / ((w + 1) * (w + 2)))
  · exact indexedSquaredRamp_measurable
      (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
      (divisorWindowIndex gaussianIndexAddress)
  · exact archivedGaussianSquaredWindow_growth
  · intro w hw
    exact analyticAt_const.div
      ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
      (squaredWindowDenominator_ne_zero (by linarith))
  · intro w hw
    exact div_ne_zero (by norm_num) (squaredWindowDenominator_ne_zero (by linarith))
  · exact fun _ hw => archivedGaussianSquaredWindow_mellin hw
  · exact hcut

#print axioms archivedGaussianSquaredWindow_eq_sum
#print axioms archivedGaussianSquaredWindow_growth
#print axioms archivedGaussianSquaredWindow_mellin
#check quartic_rh_of_archived_gaussian_prefix_windows
#print axioms quartic_rh_of_archived_gaussian_prefix_windows
#check quartic_rh_of_archived_gaussian_squared_windows
#print axioms quartic_rh_of_archived_gaussian_squared_windows

end
end AlpogeSuperZeta
