import DottieRationalWeight
import Mathlib.Analysis.Complex.Liouville

namespace FieldTarget

open Complex Metric Set

/-- The coefficient bound for a centered polynomial on a disk of radius `ρ`.
Each complex coefficient is bounded by the sum of its two absolute parts. -/
def dottieWeightCoefficientBound {N : ℕ} (a : Fin N → ℚ × ℚ) (ρ : ℝ) : ℝ :=
  ∑ k : Fin N, (abs ((a k).1 : ℝ) + abs ((a k).2 : ℝ)) * ρ ^ (k : ℕ)

theorem dottieWeightCoefficientBound_nonneg {N : ℕ} (a : Fin N → ℚ × ℚ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 ≤ dottieWeightCoefficientBound a ρ := by
  unfold dottieWeightCoefficientBound
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (by positivity) (pow_nonneg hρ _))

theorem norm_dottieRationalWeight_le {N : ℕ} (a : Fin N → ℚ × ℚ)
    {c z : ℂ} {ρ : ℝ} (hz : z ∈ closedBall c ρ) :
    ‖dottieRationalWeight c a z‖ ≤ dottieWeightCoefficientBound a ρ := by
  have hDist : ‖z - c‖ ≤ ρ := (dist_eq_norm z c) ▸ mem_closedBall.mp hz
  unfold dottieRationalWeight dottieWeightCoefficientBound
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [norm_mul, norm_pow]
  have hCoeff : ‖((a k).1 : ℝ) + I * ((a k).2 : ℝ)‖ ≤
      abs ((a k).1 : ℝ) + abs ((a k).2 : ℝ) := by
    refine (norm_add_le (↑((a k).1 : ℝ) : ℂ) (I * ((a k).2 : ℝ))).trans_eq ?_
    rw [norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul hCoeff (pow_le_pow_left₀ (norm_nonneg _) hDist _) (by positivity)
    (by positivity)

/-- A bound for the derivative of the weighted reading on the measuring disk
from a bound for the unweighted reading on the larger disk. -/
theorem norm_deriv_dottieRationalWeight_mul_le {N : ℕ} (a : Fin N → ℚ × ℚ)
    {F : ℂ → ℂ} {c z : ℂ} {r ρ B : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ)
    (hF : DifferentiableOn ℂ F (closedBall c ρ))
    (hBound : ∀ v ∈ closedBall c ρ, ‖F v‖ ≤ B) (hz : z ∈ closedBall c r) :
    ‖deriv (dottieRationalWeight c a * F) z‖ ≤
      dottieWeightCoefficientBound a ρ * B / (ρ - r) := by
  have hd : 0 < ρ - r := sub_pos.mpr hrρ
  have hLocal : closedBall z (ρ - r) ⊆ closedBall c ρ := by
    intro v hv
    apply mem_closedBall.mpr
    refine (dist_triangle v z c).trans ?_
    linarith only [mem_closedBall.mp hv, mem_closedBall.mp hz]
  have hReg := ((dottieRationalWeight_differentiable c a).differentiableOn.mul hF).mono hLocal
  rw [← closure_ball z hd.ne'] at hReg
  refine norm_deriv_le_of_forall_mem_sphere_norm_le hd hReg.diffContOnCl ?_
  intro v hv
  have hvOuter := hLocal (sphere_subset_closedBall hv)
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (norm_dottieRationalWeight_le a hvOuter) (hBound v hvOuter)
    (norm_nonneg _) (dottieWeightCoefficientBound_nonneg a (hr.trans hrρ.le))

#print axioms dottieWeightCoefficientBound_nonneg
#print axioms norm_dottieRationalWeight_le
#print axioms norm_deriv_dottieRationalWeight_mul_le

end FieldTarget
