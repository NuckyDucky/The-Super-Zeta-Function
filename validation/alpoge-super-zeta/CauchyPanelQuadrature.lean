import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Error of a positive quadrature rule from Cauchy's power series bounds. -/
noncomputable section

namespace SuperZeta.CauchyPanelQuadrature

open Complex MeasureTheory Set
open scoped BigOperators NNReal ENNReal

private def coefficient (f : ℂ → ℂ) (R : ℝ≥0) (k : ℕ) : ℂ :=
  (cauchyPowerSeries f 0 R k) (fun _ => 1)

private theorem coefficient_bound {f : ℂ → ℂ} {R : ℝ≥0} {M : ℝ}
    (hM : ∀ z ∈ Metric.sphere 0 (R:ℝ), ‖f z‖ ≤ M) (k : ℕ) :
    ‖coefficient f R k‖ ≤ M * ((R:ℝ)⁻¹)^k := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2*Real.pi) (f := fun θ : ℝ => ‖f (circleMap 0 R θ)‖)
    (C := M) (fun θ _ => by simpa only [norm_norm] using hM _ (circleMap_mem_sphere 0 R.2 θ))
  have hJ : (∫ θ : ℝ in (0:ℝ)..(2*Real.pi), ‖f (circleMap 0 R θ)‖) ≤ 2*Real.pi*M := by
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at hi
    exact (le_abs_self _).trans (by simpa only [mul_comm] using hi)
  have hC := norm_cauchyPowerSeries_le f 0 R k
  have hRabs : |(R:ℝ)| = (R:ℝ) := abs_of_nonneg R.2
  rw [hRabs] at hC
  calc
    _ ≤ ‖cauchyPowerSeries f 0 R k‖ := by
      simpa only [coefficient, norm_one, Finset.prod_const_one, mul_one] using
        (cauchyPowerSeries f 0 R k).le_opNorm (fun _ => (1:ℂ))
    _ ≤ ((2*Real.pi)⁻¹ * (2*Real.pi*M))*((R:ℝ)⁻¹)^k := by
      apply hC.trans
      gcongr
    _ = _ := by rw [inv_mul_cancel_left₀ Real.two_pi_pos.ne']

private theorem cauchy_apply (f : ℂ → ℂ) (R : ℝ≥0) (k : ℕ) (z : ℂ) :
    (cauchyPowerSeries f 0 R k) (fun _ => z) = coefficient f R k*z^k := by
  simp [coefficient, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    smul_eq_mul, mul_comm]

private def truncation (f : ℂ → ℂ) (R : ℝ≥0) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, coefficient f R k * (x:ℂ)^k

private theorem cauchy_truncation_error {f : ℂ → ℂ} {R : ℝ≥0} {M : ℝ}
    (hR : 1 < R) (hf : DifferentiableOn ℂ f (Metric.closedBall 0 (R:ℝ)))
    (hM : ∀ z ∈ Metric.sphere 0 (R:ℝ), ‖f z‖ ≤ M)
    (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖f (x:ℂ)-truncation f R n x‖ ≤ M*((R:ℝ)⁻¹)^n/(1-(R:ℝ)⁻¹) := by
  let q := (R:ℝ)⁻¹
  have hR' : (1:ℝ) < R := hR
  have hq₀ : 0 ≤ q := inv_nonneg.mpr R.2
  have hq₁ : q < 1 := inv_lt_one_of_one_lt₀ hR'
  let a := fun k => coefficient f R k*(x:ℂ)^k
  have hn (k : ℕ) : ‖a k‖ ≤ M*q^k := by
    unfold a
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg x) hx) |>.trans
      (coefficient_bound hM k)
  have hxR : (x:ℂ) ∈ EMetric.ball 0 (R:ℝ≥0∞) := by
    rw [EMetric.mem_ball, edist_zero_right, ← ofReal_norm, norm_real, Real.norm_eq_abs]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < R)).mpr (hx.trans_lt hR')
  have hs : HasSum a (f (x:ℂ)) := by
    simpa only [zero_add, cauchy_apply, a] using
      (hf.hasFPowerSeriesOnBall (zero_lt_one.trans hR)).hasSum hxR
  have ht : HasSum (fun j => a (j+n)) (f (x:ℂ) - truncation f R n x) :=
    (hasSum_nat_add_iff' n).mpr hs
  let b := fun j : ℕ => (M*q^n)*q^j
  have hb (j : ℕ) : ‖a (j+n)‖ ≤ b j := by
    exact (hn (j+n)).trans_eq (by simp only [b, pow_add]; ring)
  have hsb : Summable b := (summable_geometric_of_lt_one hq₀ hq₁).mul_left _
  have hsa : Summable (fun j => ‖a (j+n)‖) := hsb.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [← ht.tsum_eq]
  calc
    _ ≤ ∑' j, ‖a (j+n)‖ := norm_tsum_le_tsum_norm hsa
    _ ≤ ∑' j, b j := hsa.tsum_le_tsum hb hsb
    _ = _ := by
      simp only [b, tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁, div_eq_mul_inv]
      rfl

/-- If the real weights are nonnegative and match the first \(n\) moments,
the error on the unit interval is at most four times the Cauchy tail.
Both endpoints are included in the node bounds. -/
theorem error_unit {ι : Type*} (nodes : Finset ι) (x w : ι → ℝ)
    (hx : ∀ j ∈ nodes, |x j| ≤ 1) (hw : ∀ j ∈ nodes, 0 ≤ w j)
    (hsum : ∑ j ∈ nodes, w j = 2)
    {n : ℕ}
    (matchMoments : ∀ k < n,
      ∑ j ∈ nodes, w j*(x j)^k = (1-(-1:ℝ)^(k+1))/(k+1))
    {f : ℂ → ℂ} {R : ℝ≥0} {M : ℝ}
    (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 (R:ℝ)))
    (hM : ∀ z ∈ Metric.sphere 0 (R:ℝ), ‖f z‖ ≤ M) :
    ‖(∫ u in (-1:ℝ)..1, f (u:ℂ)) - ∑ j ∈ nodes, (w j:ℂ)*f (x j:ℂ)‖ ≤
      4*M*((R:ℝ)⁻¹)^n/(1-(R:ℝ)⁻¹) := by
  let p := truncation f R n
  let B := M*((R:ℝ)⁻¹)^n/(1-(R:ℝ)⁻¹)
  have hB (u : ℝ) (hu : |u| ≤ 1) : ‖f (u:ℂ)-p u‖ ≤ B :=
    cauchy_truncation_error hR hf hM n hu
  have hR' : (1:ℝ) < R := hR
  have hIntF : IntervalIntegrable (fun u : ℝ => f (u:ℂ)) volume (-1) 1 :=
    (hf.continuousOn.comp continuous_ofReal.continuousOn (fun u hu => by
      rw [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      have h := (mem_Icc.mp hu)
      exact ((abs_le.mpr ⟨h.1,h.2⟩) : |u| ≤ 1).trans hR'.le)).intervalIntegrable_of_Icc
      (by norm_num)
  have hp : Continuous p := by unfold p truncation; fun_prop
  have hIntP := hp.intervalIntegrable (μ := volume) (-1) 1
  have hintegral :
      ‖(∫ u in (-1:ℝ)..1, f (u:ℂ)) - ∫ u in (-1:ℝ)..1, p u‖ ≤ 2*B := by
    rw [← intervalIntegral.integral_sub hIntF hIntP]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1:ℝ)) (b := 1)
      (fun u hu => hB u (by
        rw [uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hu
        exact abs_le.mpr ⟨hu.1.le,hu.2⟩))
    simpa only [show |(1:ℝ)-(-1)| = 2 by norm_num, mul_comm B] using h
  have hpExact : (∫ u in (-1:ℝ)..1, p u) = ∑ j ∈ nodes, (w j:ℂ)*p (x j) := by
    unfold p truncation
    have hint (k : ℕ) : IntervalIntegrable (fun u : ℝ => coefficient f R k * (u:ℂ)^k) volume (-1) 1 :=
      (by fun_prop : Continuous (fun u : ℝ => coefficient f R k * (u:ℂ)^k)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finset_sum (fun k _ => hint k)]
    simp only [intervalIntegral.integral_const_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (∫ u in (-1:ℝ)..1, (u:ℂ)^k) =
      (((1-(-1:ℝ)^(k+1))/(k+1):ℝ):ℂ) by
        simp_rw [← Complex.ofReal_pow, intervalIntegral.integral_ofReal, integral_pow, one_pow]]
    rw [← matchMoments k (Finset.mem_range.mp hk)]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnodes :
      ‖(∑ j ∈ nodes, (w j:ℂ)*p (x j)) - ∑ j ∈ nodes, (w j:ℂ)*f (x j:ℂ)‖ ≤ 2*B := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ nodes, w j*B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_sub, norm_mul, norm_sub_rev, norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j hj)]
        exact mul_le_mul_of_nonneg_left (hB (x j) (hx j hj)) (hw j hj)
      _ = _ := by rw [← Finset.sum_mul, hsum]
  rw [← hpExact] at hnodes
  have h := norm_sub_le (∫ u in (-1:ℝ)..1, f (u:ℂ) - p u)
    ((∑ j ∈ nodes, (w j:ℂ)*f (x j:ℂ)) - ∫ u in (-1:ℝ)..1, p u)
  rw [intervalIntegral.integral_sub hIntF hIntP, sub_sub_sub_cancel_right] at h
  have ht : ‖(∑ j ∈ nodes, (w j:ℂ)*f (x j:ℂ)) - ∫ u in (-1:ℝ)..1, p u‖ ≤ 2*B := by
    rw [norm_sub_rev]
    exact hnodes
  have hscale : 4*B = 4*M*((R:ℝ)⁻¹)^n/(1-(R:ℝ)⁻¹) := by
    dsimp [B]
    ring
  rw [← hscale]
  linarith only [h, hintegral, ht]

#print axioms error_unit

end SuperZeta.CauchyPanelQuadrature
end
