import QuarticCertificateFromCells

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace QuarticKernel

private theorem theta_continuous_from {c : ℝ} (hc : 0 < c) :
    ContinuousOn theta (Ici c) := by
  unfold theta
  let r := Real.exp (-c)
  have hr : ‖r‖ < 1 := by
    rw [show ‖r‖ = Real.exp (-c) by simp [r, Real.norm_eq_abs],
      Real.exp_lt_one_iff]
    linarith
  refine continuousOn_tsum (fun n => by fun_prop)
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable ?_
  intro n x hx
  have hrs : Real.exp (-x) ≤ r := Real.exp_le_exp.mpr (neg_le_neg hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-x)^n)]
  exact mul_le_mul (coeff_abs_le n) (pow_le_pow_left₀ (by positivity) hrs n)
    (by positivity) (by positivity)

private theorem theta_continuous_positive : ContinuousOn theta (Ioi 0) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  have h : 0 < x := hx
  refine ⟨Ioi (x/2), isOpen_Ioi, by simpa only [mem_Ioi] using (by linarith : x/2 < x),
    (theta_continuous_from (show 0 < x/2 by positivity)).mono ?_⟩
  intro y hy
  exact (show x/2 < y from hy.2).le

private theorem exponential_decay :
    (fun t : ℝ => (theta (t/scale) : ℂ)) =O[atTop] fun t => Real.exp (-(1/scale)*t) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (2*scale)] with t ht
  have hu : 2 ≤ t/scale := (le_div_iff₀ scale_pos).2 ht
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (theta_abs_le (by linarith : 0 < t/scale)).trans ?_
  have he : -(1/scale)*t = -(t/scale) := by ring
  rw [he]
  exact (geometric_majorant hu).le

private theorem center_bound
    (hf : ∀ t : ℝ, 0 < t → theta (t/scale) = t⁻¹ * theta (t⁻¹/scale)) :
    (fun t : ℝ => (theta (t/scale) : ℂ)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0:ℝ))) := by
  apply IsBigO.of_bound (2*scale)
  have hs : 0 < 2*scale := mul_pos (by norm_num) scale_pos
  have hlt : ∀ᶠ (t : ℝ) in 𝓝[>] 0, t < 1/(2*scale) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hs))
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht'
  have ht₀ : 0 < t := ht
  have hu : 2 ≤ t⁻¹/scale := by
    apply (le_div_iff₀ scale_pos).2
    rw [le_inv_comm₀ hs ht₀]
    simpa only [one_div] using ht'.le
  let u := t⁻¹/scale
  have hb := (theta_abs_le (by linarith : 0 < u)).trans (geometric_majorant hu).le
  have hex : u * Real.exp (-u) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), one_mul]
    linarith [Real.add_one_le_exp u]
  have hscale : t⁻¹ = scale*u := by
    dsimp [u]
    field_simp [scale_pos.ne']
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, hf t ht₀, abs_mul, abs_of_pos (inv_pos.mpr ht₀)]
  calc
    _ ≤ t⁻¹ * (2*Real.exp (-u)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht₀.le)
    _ = (2*scale)*(u*Real.exp (-u)) := by rw [hscale]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hex hs.le

theorem mellin_differentiable_from_center (hc : theta (1/scale) ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin fun t : ℝ => (theta (t/scale) : ℂ)) s := by
  have hp : ContinuousOn (fun t : ℝ => (theta (t/scale) : ℂ)) (Ioi 0) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    refine theta_continuous_positive.comp (continuous_id.div_const scale).continuousOn ?_
    exact fun x hx => div_pos (mem_Ioi.mp hx) scale_pos
  exact mellin_differentiableAt_of_isBigO_rpow_exp (one_div_pos.mpr scale_pos)
    (hp.locallyIntegrableOn measurableSet_Ioi) exponential_decay
    (center_bound (theta_reflection_of_center_nonzero hc)) hs

#print axioms mellin_differentiable_from_center

end QuarticKernel
