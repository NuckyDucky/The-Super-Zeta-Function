import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace FieldTarget

open Complex MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The scalar coefficients of the Cauchy power series at `c`. -/
def contourTaylorCoeff (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  cauchyPowerSeries F c R n fun _ => 1

private theorem contourTaylor_hasSum {F : ℂ → ℂ} {c x : ℂ} {R : ℝ≥0}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F (closedBall c R)) (hx : ‖x‖ < (R : ℝ)) :
    HasSum (fun n => contourTaylorCoeff F c R n * x ^ n) (F (c + x)) := by
  have hmem : x ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    exact NNReal.coe_lt_coe.mp hx
  convert (hF.hasFPowerSeriesOnBall hR).hasSum hmem using 1
  ext n
  simp [contourTaylorCoeff, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, mul_comm]

theorem norm_contourTaylorCoeff_le {F : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hF : ContinuousOn F (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖F z‖ ≤ M) (n : ℕ) :
    ‖contourTaylorCoeff F c R n‖ ≤ M * R⁻¹ ^ n := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hc : Continuous (fun θ => ‖F (circleMap c R θ)‖) :=
    (hF.comp_continuous (continuous_circleMap c R)
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ))).norm
  have hInt : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap c R θ)‖) ≤ (2 * Real.pi) * M := by
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      intervalIntegral.integral_mono_on (μ := volume) hπ.le (hc.intervalIntegrable _ _)
        (intervalIntegrable_const (c := M)) (fun θ _ => hM _ (circleMap_mem_sphere c hR.le θ))
  have havg : (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap c R θ)‖) ≤ M := by
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hπ).mpr ((mul_comm M (2 * Real.pi)) ▸ hInt)
  calc
    _ ≤ ‖cauchyPowerSeries F c R n‖ := by simp [contourTaylorCoeff]
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap c R θ)‖) * R⁻¹ ^ n := by
      simpa only [abs_of_pos hR] using norm_cauchyPowerSeries_le F c R n
    _ ≤ _ := mul_le_mul_of_nonneg_right havg (by positivity)

/-- The Taylor truncation is uniformly accurate on every smaller closed disk. -/
theorem contourTaylor_tail_le {F : ℂ → ℂ} {c x : ℂ} {R : ℝ≥0} {r M : ℝ}
    (hF : DifferentiableOn ℂ F (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖F z‖ ≤ M) (hr : r < (R : ℝ)) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖F (c + x) - ∑ k ∈ Finset.range n, contourTaylorCoeff F c R k * x ^ k‖ ≤
      M * (r / (R : ℝ)) ^ n / (1 - r / (R : ℝ)) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  have hR : 0 < (R : ℝ) := hr0.trans_lt hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (circleMap_mem_sphere c hR.le 0))
  let q := r / (R : ℝ)
  have hq0 : 0 ≤ q := div_nonneg hr0 hR.le
  have hq : q < 1 := (div_lt_one hR).mpr hr
  let terms := fun k : ℕ => contourTaylorCoeff F c R k * x ^ k
  have hsum : HasSum terms (F (c + x)) := contourTaylor_hasSum (by exact_mod_cast hR) hF (hx.trans_lt hr)
  have htail : F (c + x) - ∑ k ∈ Finset.range n, terms k = ∑' k : ℕ, terms (k + n) := by
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add n, add_sub_cancel_left]
  change ‖F (c + x) - ∑ k ∈ Finset.range n, terms k‖ ≤ M * q ^ n / (1 - q)
  rw [htail, div_eq_mul_inv]
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq).mul_left (M * q ^ n))
  intro k
  dsimp [terms]
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (M * (R : ℝ)⁻¹ ^ (k + n)) * r ^ (k + n) := by
      gcongr
      exact norm_contourTaylorCoeff_le hR hF.continuousOn hM _
    _ = (M * q ^ n) * q ^ k := by
      simp only [q, div_eq_mul_inv, mul_pow, pow_add]
      ring

#print axioms norm_contourTaylorCoeff_le
#print axioms contourTaylor_tail_le

end

end FieldTarget
