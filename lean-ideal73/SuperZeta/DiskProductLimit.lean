import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Order.Interval.Set.Infinite

/-! Finite disks exhaust a spectral list with summable reciprocal norms.
The reflected factors used to cancel its zeros tend to one. -/
namespace SuperZeta.DiskProduct

open Filter Set
open scoped Topology

private theorem finite_roots {ι : Type*} {l : ι → ℂ}
    (hl : ∀ i, l i ≠ 0) (hs : Summable (fun i => ‖l i‖⁻¹))
    {R : ℝ} (hR : 0 < R) : {i | ‖l i‖ < R}.Finite := by
  have hf := hs.tendsto_cofinite_zero.eventually_lt_const (inv_pos.mpr hR)
  rw [Filter.eventually_cofinite] at hf
  apply hf.subset
  intro i hi h
  exact (not_lt_of_gt ((inv_lt_inv₀ hR (norm_pos_iff.mpr (hl i))).mpr hi)) h

private theorem mirror_limit {ι : Type*} {l : ι → ℂ} (hl : ∀ i, l i ≠ 0)
    (hs : Summable (fun i => ‖l i‖⁻¹)) {R : ℕ → ℝ} {S : ℕ → Finset ι}
    (hpos : ∀ k, 0 < R k) (hinf : Tendsto R atTop atTop)
    (hS : ∀ k i, i ∈ S k ↔ ‖l i‖ < R k) (z : ℂ) :
    Tendsto (fun k => ∏ i ∈ S k, (1 - star (l i) * z / (R k : ℂ)^2)) atTop (𝓝 1) := by
  classical
  let x (k : ℕ) (i : ι) := -(star (l i) * z / (R k : ℂ)^2)
  have hx (k i) : ‖x k i‖ = ‖l i‖ * ‖z‖ / (R k)^2 := by
    simp [x, norm_pow, Real.norm_eq_abs, abs_of_pos (hpos k)]
  let a (k : ℕ) (i : ι) := if i ∈ S k then ‖x k i‖ else 0
  have point (i : ι) : Tendsto (fun k => a k i) atTop (𝓝 0) := by
    have h : Tendsto (fun k => ‖l i‖ * ‖z‖ / (R k)^2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hinf)
    apply h.congr'
    filter_upwards [hinf.eventually_gt_atTop ‖l i‖] with k hk
    simp [a, (hS k i).mpr hk, hx]
  have bound (k i) : ‖a k i‖ ≤ ‖z‖ * ‖l i‖⁻¹ := by
    have hn := norm_pos_iff.mpr (hl i)
    by_cases hi : i ∈ S k
    · have hsmall := (hS k i).mp hi
      change ‖(if i ∈ S k then ‖x k i‖ else 0 : ℝ)‖ ≤ _
      rw [if_pos hi, Real.norm_of_nonneg (norm_nonneg _), hx]
      calc
        ‖l i‖ * ‖z‖ / R k ^ 2 = ‖z‖ * (‖l i‖ / R k ^ 2) := by ring
        _ ≤ ‖z‖ * ‖l i‖⁻¹ := by
          gcongr
          rw [div_le_iff₀ (sq_pos_of_pos (hpos k)), ← div_eq_inv_mul, le_div_iff₀ hn]
          nlinarith
    · simp [a, hi, mul_nonneg]
  have ha := tendsto_tsum_of_dominated_convergence (hs.mul_left ‖z‖) point
    (Eventually.of_forall bound)
  have heq (k) : (∑' i, a k i) = ∑ i ∈ S k, ‖x k i‖ := by
    rw [tsum_eq_sum (s := S k) (fun i hi => by simp [a, hi])]
    exact Finset.sum_congr rfl (fun i hi => by simp [a, hi])
  simp only [heq, tsum_zero] at ha
  have hzero := (Real.continuous_exp.tendsto 0 |>.comp ha).sub (tendsto_const_nhds (x := (1 : ℝ)))
  rw [Real.exp_zero, sub_self] at hzero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hzero
  intro k
  simpa only [x, sub_eq_add_neg, Function.comp_apply] using
    (S k).norm_prod_one_add_sub_one_le (x k)

/-- Radii escaping to infinity, each with an empty boundary, together
with the finite products and their reflected-factor limit. -/
theorem exists_exhaustion {ι : Type*} (l : ι → ℂ) (hl : ∀ i, l i ≠ 0)
    (hs : Summable (fun i => ‖l i‖⁻¹)) :
    ∃ (R : ℕ → ℝ) (S : ℕ → Finset ι),
      (∀ k, 0 < R k) ∧ Tendsto R atTop atTop ∧
      (∀ k i, i ∈ S k ↔ ‖l i‖ < R k) ∧ (∀ k i, ‖l i‖ ≠ R k) ∧
      Tendsto S atTop atTop ∧ ∀ z : ℂ,
        Tendsto (fun k => ∏ i ∈ S k, (1 - star (l i) * z / (R k : ℂ)^2)) atTop (𝓝 1) := by
  classical
  have exists_radius (k : ℕ) : ∃ r : ℝ, (k : ℝ) + 1 < r ∧ r < k + 2 ∧ ∀ i, ‖l i‖ ≠ r := by
    let A := {i | ‖l i‖ < (k : ℝ) + 2}
    have hA : A.Finite := finite_roots hl hs (by positivity)
    have hB := hA.image (fun i => ‖l i‖)
    have he := Set.Ioo_infinite (show (k : ℝ)+1 < k+2 by linarith)
    have hsub : ¬ Set.Ioo ((k : ℝ)+1) (k+2) ⊆ (fun i => ‖l i‖) '' A :=
      fun h => he (hB.subset h)
    obtain ⟨r, hr, h⟩ := Set.not_subset.mp hsub
    exact ⟨r, hr.1, hr.2, fun i e => h ⟨i, by simpa [A, e] using hr.2, e⟩⟩
  choose R hlo hhi hav using exists_radius
  have hpos (k) : 0 < R k := lt_trans (by positivity) (hlo k)
  have hinf : Tendsto R atTop atTop := tendsto_atTop_mono (fun k => by
    exact (le_trans (by simp : (k:ℝ) ≤ k + 1) (hlo k).le)) tendsto_natCast_atTop_atTop
  let S (k : ℕ) := (finite_roots hl hs (hpos k)).toFinset
  have hS (k i) : i ∈ S k ↔ ‖l i‖ < R k := by simp [S]
  refine ⟨R, S, hpos, hinf, hS, hav, ?_, mirror_limit hl hs hpos hinf hS⟩
  rw [tendsto_atTop]
  intro a
  exact (a.eventually_all (p := fun i k => i ∈ S k)).mpr fun i _ =>
    (hinf.eventually_gt_atTop ‖l i‖).mono fun k hk => (hS k i).mpr hk

end SuperZeta.DiskProduct
