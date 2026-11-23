import SuperZeta.ReferenceProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Real.Pi.Bounds

/-! Resolvent of the squared reference determinant on the positive ray. -/
namespace SuperZeta.Reference
noncomputable section
open Filter Set
open scoped Topology

private lemma mode_pos (n : ℕ) : 0 < eigenvalue n := by unfold eigenvalue; positivity

private lemma inverse_modes_summable : Summable (fun n : ℕ => 1 / eigenvalue n) := by
  have major := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr one_lt_two)
  apply Summable.of_nonneg_of_le (fun n => (one_div_pos.mpr (mode_pos n)).le) _ major
  intro n
  change 1 / eigenvalue n ≤ 1 / ((n+1:ℕ):ℝ)^2
  apply one_div_le_one_div_of_le (by positivity)
  unfold eigenvalue
  apply pow_le_pow_left₀ (by positivity) _ 2
  push_cast
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [Real.pi_gt_three, mul_nonneg (show 0 ≤ Real.pi-1 by linarith [Real.pi_gt_three]) hn]

private lemma mode_log_summable (x : ℝ) :
    Summable (fun n : ℕ => Real.log (1+x/eigenvalue n)) := by
  apply Real.summable_log_one_add_of_summable
  simpa only [mul_one_div] using inverse_modes_summable.mul_left x

/-- Logarithmic differentiation of the positive-ray reference determinant.
Each eigenvalue contributes twice, corresponding to its multiplicity. -/
theorem reference_resolvent {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => Real.log ((Real.cosh (Real.sqrt y))^2))
      (∑' n : ℕ, 2/(t+eigenvalue n)) t := by
  let f := fun (n : ℕ) (y : ℝ) => Real.log (1+y/eigenvalue n)
  let g := fun (n : ℕ) (y : ℝ) => 1/(y+eigenvalue n)
  have hd (n : ℕ) (y : ℝ) (hy : y ∈ Ioi 0) : HasDerivAt (f n) (g n y) y := by
    have hl := mode_pos n
    have hy' : 0 < y := hy
    have deriv := ((hasDerivAt_const y (1:ℝ)).add ((hasDerivAt_id y).div_const (eigenvalue n))).log
      (by change 1+y/eigenvalue n ≠ 0; positivity)
    convert deriv using 1
    · rfl
    · change 1 / (y + eigenvalue n) = (0 + 1 / eigenvalue n) / (1 + y / eigenvalue n)
      field_simp
      ring
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Ioi 0) : ‖g n y‖ ≤ 1/eigenvalue n := by
    have hl := mode_pos n
    have hy' : 0 < y := hy
    dsimp only [g]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le hl (by linarith)
  have ds := hasDerivAt_tsum_of_isPreconnected inverse_modes_summable isOpen_Ioi
    isPreconnected_Ioi hd hb ht (mode_log_summable t) ht
  have hlog {y : ℝ} (hy : 0 < y) : Real.log (Real.cosh (Real.sqrt y)) = ∑' n, f n y := by
    have h := reference_ray_product (Real.sqrt y)
    simp only [Real.sq_sqrt hy.le] at h
    have hplus (n : ℕ) : 0 < 1+y/eigenvalue n := by have := mode_pos n; positivity
    have exp_eq := h.unique (Real.hasProd_of_hasSum_log hplus (mode_log_summable y).hasSum)
    simpa [f] using congrArg Real.log exp_eq
  have dh := ds.const_mul 2
  have ht' : 2*(∑' n, g n t) = ∑' n : ℕ, 2/(t+eigenvalue n) := by
    rw [← tsum_mul_left]
    simp [g, div_eq_mul_inv]
  rw [← ht']
  apply dh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with y hy
  simp only [Real.log_pow, hlog hy, Nat.cast_ofNat]

end
end SuperZeta.Reference
