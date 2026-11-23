import ArchivedDottieRangeIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A common Gaussian majorant for the exact finite contour on a compact
parameter disk, and a derivative majorant on a smaller disk. -/

namespace QuarticModel

open Complex Finset MeasureTheory Metric Set
open private dottie_range_integrand_eq from ArchivedDottieRangeIntegral
open private norm_dottieContourIntegrand_le dottieContourMajorant
  from ArchivedDottieTailPartition

private noncomputable def rangeMajorantFactor (S : Finset ℕ) (w : ℂ) : ℝ :=
  ∑ n ∈ S, ‖(archivedLatticeCoeff n : ℂ)‖ *
    ((archivedThetaScale/(n : ℝ))^(w.re+1) * Real.Gamma (w.re+1) *
      Real.exp (1+Real.pi^2/8))

private theorem range_integrand_norm_le (S : Finset ℕ) {w : ℂ} (hw : 0 < w.re+1)
    (hS : ∀ n ∈ S, n ≠ 0) (u : ℝ) :
    ‖dottieRangeIntegrand S w u‖ ≤ rangeMajorantFactor S w * Real.exp (-((1/2 : ℝ)*u^2)) := by
  rw [dottie_range_integrand_eq, rangeMajorantFactor, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_dottieContourIntegrand_le hw (hS n hn) u) (norm_nonneg _)

private theorem positive_on_contour_ball {w : ℂ} {R : ℝ} (hR : R < w.re+1)
    {x : ℂ} (hx : x ∈ closedBall w R) : 0 < x.re+1 := by
  have hnorm : ‖x-w‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hre := (Complex.abs_re_le_norm (x-w)).trans hnorm
  rw [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1, hR]

theorem dottie_range_contour_uniform_value_bound (S : Finset ℕ) (w : ℂ) (R : ℝ)
    (hR : R < w.re+1) (hS : ∀ n ∈ S, n ≠ 0) :
    ∃ C : ℝ, ∀ x ∈ closedBall w R, ∀ u : ℝ,
      ‖dottieRangeIntegrand S x u‖ ≤ C * Real.exp (-((1/2 : ℝ)*u^2)) := by
  have hRe : Continuous (fun x : ℂ => x.re+1) := continuous_re.add continuous_const
  have hGamma : ContinuousOn (fun x : ℂ => Real.Gamma (x.re+1)) (closedBall w R) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp hRe.continuousOn
      (fun _ hx => positive_on_contour_ball hR hx)
  have hfactor : ContinuousOn (rangeMajorantFactor S) (closedBall w R) := by
    unfold rangeMajorantFactor
    refine continuousOn_finsetSum S (fun n hn => ?_)
    have hbase : 0 < archivedThetaScale/(n : ℝ) :=
      div_pos archivedThetaScale_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hS n hn)))
    have hpow := ((Real.continuous_const_rpow hbase.ne').comp hRe).continuousOn (s := closedBall w R)
    exact continuousOn_const.mul ((hpow.mul hGamma).mul continuousOn_const)
  obtain ⟨C,hC⟩ := (isCompact_closedBall w R).exists_bound_of_continuousOn hfactor
  refine ⟨C, fun x hx u => ?_⟩
  refine (range_integrand_norm_le S (positive_on_contour_ball hR hx) hS u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)

theorem dottie_range_contour_derivative_bound
    (S : Finset ℕ) (w : ℂ) (R : ℝ) (hR : 0 < R) (hpos : 2*R < w.re+1)
    (hS : ∀ n ∈ S, n ≠ 0)
    (hd : ∀ u : ℝ, ∀ x ∈ closedBall w (2*R),
      DifferentiableAt ℂ (fun v => dottieRangeIntegrand S v u) x) :
    ∃ C : ℝ, ∀ u : ℝ, ∀ x ∈ ball w R,
      ‖deriv (fun v => dottieRangeIntegrand S v u) x‖ ≤ C * Real.exp (-((1/2 : ℝ)*u^2)) := by
  obtain ⟨C,hC⟩ := dottie_range_contour_uniform_value_bound S w (2*R) hpos hS
  refine ⟨C/R, fun u x hx => ?_⟩
  have hsub : closedBall x R ⊆ closedBall w (2*R) := by
    intro v hv
    rw [mem_closedBall] at hv ⊢
    have hdist := dist_triangle v x w
    have hx' := mem_ball.mp hx
    linarith
  have hdisc : DiffContOnCl ℂ (fun v => dottieRangeIntegrand S v u) (ball x R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact fun v hv => (hd u v (hsub hv)).differentiableWithinAt
  have hb : ∀ v ∈ sphere x R,
      ‖dottieRangeIntegrand S v u‖ ≤ C * Real.exp (-((1/2 : ℝ)*u^2)) := by
    exact fun v hv => hC v (hsub (mem_closedBall.mpr (mem_sphere.mp hv).le)) u
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdisc hb).trans_eq ?_
  ring

#print axioms dottie_range_contour_uniform_value_bound
#print axioms dottie_range_contour_derivative_bound

end QuarticModel
