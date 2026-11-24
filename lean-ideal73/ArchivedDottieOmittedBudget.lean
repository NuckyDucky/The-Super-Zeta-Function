import ArchivedDottieFiniteSums
import Batteries.Tactic.OpenPrivate

/-! Split the exact omitted sum into a lower range, a middle range, and a
finite far range. The lower range is expressed as its weight-one block
plus its smoothing error. The numerical estimates enter as hypotheses. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private dottieSharpSide from ArchivedDottieTailPartition

def dottieOmittedSharpEnd : ℕ := 10_000_000_000_000

def dottieOmittedFarCut : ℕ := 2 * 10^25

/-- The weight-one block for the omitted norms through `10^13`. -/
noncomputable def dottieOmittedSharpBlock (w : ℂ) : ℂ :=
  ∑ n ∈ Ioc dottiePrefixEnd dottieOmittedSharpEnd,
    (dottieSharpSide w n + conj (dottieSharpSide (1 - conj w) n))

/-- The exact smoothing correction on that same lower block. -/
noncomputable def dottieOmittedLowerSmoothingError (w : ℂ) : ℂ :=
  (∑ n ∈ Ioc dottiePrefixEnd dottieOmittedSharpEnd, dottieSmoothTerm w n) -
    dottieOmittedSharpBlock w

/-- The exact omitted terms above `10^13` through `2 * 10^25`. -/
noncomputable def dottieOmittedMiddleSmooth (w : ℂ) : ℂ :=
  ∑ n ∈ dottieOmittedNorms.filter (fun n => dottieOmittedSharpEnd < n ∧ n ≤ dottieOmittedFarCut),
    dottieSmoothTerm w n

/-- The remaining finite omitted terms above `2 * 10^25`. -/
noncomputable def dottieOmittedFarSmooth (w : ℂ) : ℂ :=
  ∑ n ∈ dottieOmittedNorms.filter (fun n => dottieOmittedFarCut < n), dottieSmoothTerm w n

private theorem dottieOmittedNorms_filter_lower :
    dottieOmittedNorms.filter (fun n => n ≤ dottieOmittedSharpEnd) =
      Ioc dottiePrefixEnd dottieOmittedSharpEnd := by
  apply Finset.ext
  intro n
  rw [Finset.mem_filter, Finset.mem_Ioc]
  simp only [dottieOmittedNorms, Finset.mem_union, Finset.mem_Ico,
    dottiePrefixEnd, dottieOmittedSharpEnd, dottieTailStart]
  omega

private theorem dottieOmitted_eq_smooth_blocks (w : ℂ) :
    dottieOmitted w =
      (∑ n ∈ Ioc dottiePrefixEnd dottieOmittedSharpEnd, dottieSmoothTerm w n) +
        dottieOmittedMiddleSmooth w + dottieOmittedFarSmooth w := by
  rw [dottie_omitted_eq_finite_sum, ← dottieOmittedNorms_filter_lower]
  unfold dottieOmittedMiddleSmooth dottieOmittedFarSmooth
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hcuts : dottieOmittedSharpEnd ≤ dottieOmittedFarCut := by decide +kernel
  rcases le_or_gt n dottieOmittedSharpEnd with hlow | hlow
  · have hfar := hlow.trans hcuts
    simp [hlow, not_lt_of_ge hlow, not_lt_of_ge hfar]
  · rcases le_or_gt n dottieOmittedFarCut with hfar | hfar
    · simp [not_le_of_gt hlow, hlow, hfar, not_lt_of_ge hfar]
    · simp [not_le_of_gt hlow, not_le_of_gt hfar, hfar]

theorem dottieOmitted_eq_sharp_add_middle_add_errors (w : ℂ) :
    dottieOmitted w =
      (dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w) +
        dottieOmittedLowerSmoothingError w + dottieOmittedFarSmooth w := by
  rw [dottieOmitted_eq_smooth_blocks, dottieOmittedLowerSmoothingError]
  abel

/-- The two absolute error budgets and the joint signed bound supply the
omitted-sum premise of the archived Dottie ring test. -/
theorem dottieOmitted_tail_of_split_budget (hS : 0 < dottieCircleReference)
    (hlower : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖dottieOmittedLowerSmoothingError w‖ ≤ (1/1000)*((w.re - 1/2)*dottieCircleReference))
    (hsigned : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmittedSharpBlock w + dottieOmittedMiddleSmooth w).im ≤
        188*((w.re - 1/2)*dottieCircleReference))
    (hfar : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖dottieOmittedFarSmooth w‖ ≤ (465/1000)*((w.re - 1/2)*dottieCircleReference)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmitted w).im ≤ 189*((w.re - 1/2)*dottieCircleReference) := by
  intro w hw
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hscale : 0 ≤ (w.re - 1/2)*dottieCircleReference :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1/2048).trans hx) hS.le
  have hlowerIm := (le_abs_self (dottieOmittedLowerSmoothingError w).im).trans
    (Complex.abs_im_le_norm _)
  have hfarIm := (le_abs_self (dottieOmittedFarSmooth w).im).trans (Complex.abs_im_le_norm _)
  rw [dottieOmitted_eq_sharp_add_middle_add_errors, Complex.add_im, Complex.add_im]
  linarith only [hsigned w hw, hlowerIm.trans (hlower w hw), hfarIm.trans (hfar w hw), hscale]

#print axioms dottieOmitted_eq_sharp_add_middle_add_errors
#print axioms dottieOmitted_tail_of_split_budget

end QuarticModel
