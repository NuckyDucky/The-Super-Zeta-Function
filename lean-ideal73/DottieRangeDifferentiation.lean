import DottieRangeDomination
import DottieRangeContourLocal
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiate the original finite range contour with its original
Gaussian tilt and its fixed completion scale. -/

namespace QuarticModel

open Complex Finset MeasureTheory Metric Set Filter
open scoped Topology
open private positive_on_contour_ball from DottieRangeDomination

/-- The derivative of one contour side uses the same signed norms and
completion scale as that side. -/
noncomputable def dottieRangeSideDerivative (S : Finset ℕ) (w : ℂ) : ℂ :=
  (∫ u : ℝ, deriv (fun v => dottieRangeIntegrand S v u) w) /
    (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ))

theorem dottie_range_side_hasDerivAt (S : Finset ℕ) {w : ℂ} (hw : 0 < w.re+1)
    (hS : ∀ n ∈ S, n ≠ 0) :
    HasDerivAt (dottieRangeSide S) (dottieRangeSideDerivative S w) w := by
  let R := (w.re+1)/4
  have hR : 0 < R := by dsimp [R]; linarith
  have hpos : 2*R < w.re+1 := by dsimp [R]; linarith
  have hxpos (x : ℂ) (hx : x ∈ ball w R) : 0 < x.re+1 := by
    apply positive_on_contour_ball hpos
    exact mem_closedBall.mpr ((mem_ball.mp hx).le.trans (by linarith))
  have hd (u : ℝ) (x : ℂ) (hx : x ∈ closedBall w (2*R)) :
      DifferentiableAt ℂ (fun v => dottieRangeIntegrand S v u) x :=
    dottie_range_integrand_differentiableAt S (positive_on_contour_ball hpos hx) hS u
  obtain ⟨C,hC⟩ := dottie_range_contour_derivative_bound S w R hR hpos hS hd
  have hFmeas : ∀ᶠ x in 𝓝 w, AEStronglyMeasurable (dottieRangeIntegrand S x) volume := by
    filter_upwards [ball_mem_nhds w hR] with x hx
    exact (dottie_range_integrand_continuous S (hxpos x hx) hS).aestronglyMeasurable
  have hbound : Integrable (fun u : ℝ => C * Real.exp (-((1/2 : ℝ)*u^2))) := by
    simp only [← neg_mul]
    exact (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/2 by norm_num)).const_mul C
  have hDeriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := dottieRangeIntegrand S) (F' := fun x u => deriv (fun v => dottieRangeIntegrand S v u) x)
    (bound := fun u : ℝ => C * Real.exp (-((1/2 : ℝ)*u^2))) (ball_mem_nhds w hR) hFmeas
    (dottie_range_integrand_integrable S hw hS)
    (dottie_range_integrand_deriv_continuous S hw hS).aestronglyMeasurable
    (Eventually.of_forall hC) hbound
    (Eventually.of_forall fun u x hx =>
      (dottie_range_integrand_differentiableAt S (hxpos x hx) hS u).hasDerivAt)
  exact hDeriv.2.div_const (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ))

#print axioms dottie_range_side_hasDerivAt

end QuarticModel
