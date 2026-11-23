import DottieRetainedFarTail
import DottieLowerFullBudget

/-! The six finite norm bands in the original Dottie circle certificate.
Each long band and its adjacent short band form one integer interval. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
set_option autoImplicit false

def dottieRetainedBandNorms : Finset ℕ :=
  Icc 1854467118035498894 1854467118035634061 ∪
  Icc 3708934236071001884 3708934236071268123 ∪
  Icc 7417868472142007863 7417868472142536246

private theorem dottie_finite_retained_partition :
    (range dottieTailStart).filter (fun n => dottieRetainedNorm n = true) =
      range (dottiePrefixEnd+1) ∪ dottieRetainedBandNorms := by
  apply Finset.ext
  intro n
  rw [Finset.mem_filter, dottieRetainedNorm, decide_eq_true_eq]
  simp only [mem_range, mem_union, mem_Icc,
    dottiePrefixEnd, dottieTailStart, dottieRetainedBandNorms]
  omega

private theorem dottie_prefix_disjoint_bands :
    Disjoint (range (dottiePrefixEnd+1)) dottieRetainedBandNorms := by
  rw [Finset.disjoint_left]
  intro n hp hb
  simp only [mem_range,dottiePrefixEnd] at hp
  simp only [dottieRetainedBandNorms,mem_union,mem_Icc] at hb
  omega

/-- Exact decomposition of the retained contribution beyond the prefix. -/
theorem dottie_retained_beyond_prefix_eq_bands_add_tail {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieRetainedBeyondPrefix w =
      (∑ n ∈ dottieRetainedBandNorms, dottieSmoothTerm w n) + dottieFarTail w := by
  have h := dottie_retained_eq_finite_add_far_tail hw₀ hw₁
  rw [dottieRetained_eq_smoothedPrefix_add_beyond hw₀ hw₁, dottieFiniteRetained,
     dottie_finite_retained_partition, sum_union dottie_prefix_disjoint_bands,
     ← dottieSmoothedPrefix, add_assoc] at h
  exact add_left_cancel h

/-- Any enclosure of just the three finite sums suffices to enclose the
full post-prefix contribution with an explicit additive allowance. -/
theorem dottie_retained_beyond_prefix_norm_le_band_bound {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) {b : ℝ}
    (hb : ‖∑ n ∈ dottieRetainedBandNorms, dottieSmoothTerm w n‖ ≤ b) :
    ‖dottieRetainedBeyondPrefix w‖ ≤ b+2/10^39 := by
  have hw₀ : 0 < w.re := by linarith only [hr.1]
  have hw₁ : w.re < 1 := by linarith only [hr.2]
  rw [dottie_retained_beyond_prefix_eq_bands_add_tail hw₀ hw₁]
  exact (norm_add_le _ _).trans
    (add_le_add hb (dottie_retained_far_tail_uniform_absolute hr hi))

/-- The archived sharp margin of 190.37 leaves an absolute budget of
3.6 × 10⁻³⁴ for the finite bands when the reference clears 2 × 10⁻³⁰. -/
theorem dottie_retained_margin_of_finite_band_bound
    (hS : 2/10^30 ≤ dottieCircleReference)
    (hsharp : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)))
    (hband : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖∑ n ∈ dottieRetainedBandNorms, dottieSmoothTerm w n‖ ≤ 36/10^35) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)) := by
  intro w hw
  obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hscale : (1/2048 : ℝ)*(2/10^30) ≤ (w.re-1/2)*dottieCircleReference :=
    mul_le_mul hx hS (by norm_num) (by linarith only [hx])
  have hp := dottie_retained_prefix_smoothing_uniform_absolute hr hi
  have hb := dottie_retained_beyond_prefix_norm_le_band_bound hr hi (hband w hw)
  have hw₀ : 0 < w.re := by linarith only [hr.1]
  have hw₁ : w.re < 1 := by linarith only [hr.2]
  have himp := (le_abs_self ((dottieSmoothedPrefix w-dottieSharpPrefix w).im)).trans
    ((Complex.abs_im_le_norm _).trans hp)
  have himb := (le_abs_self (dottieRetainedBeyondPrefix w).im).trans
    ((Complex.abs_im_le_norm _).trans hb)
  rw [dottieRetained_eq_smoothedPrefix_add_beyond hw₀ hw₁, Complex.add_im]
  rw [Complex.sub_im] at himp
  nlinarith only [hscale, himp, himb, hsharp w hw]

#print axioms dottie_retained_beyond_prefix_eq_bands_add_tail
#print axioms dottie_retained_beyond_prefix_norm_le_band_bound
#print axioms dottie_retained_margin_of_finite_band_bound

end QuarticModel
