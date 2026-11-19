import SuperZeta.DiskGrowth
import SuperZeta.DiskProductLimit
import SuperZeta.DiskRemoval
import SuperZeta.DiskRigidity

/-! The finite-disk normalization argument applies to entire functions with
an arbitrary positive constant in the square-root exponential growth bound. -/

noncomputable section

namespace SuperZeta.Factorization

open Complex Filter Metric
open scoped Topology

/-- The canonical product over the complete simple zero list of a normalized
entire function with square-root exponential growth outside the unit disk. -/
theorem eq_tprod_of_sqrt_growth {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ)
    (hE : Differentiable ℂ E) (h0 : E 0 = 1)
    (growth : ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, 1 ≤ ‖w‖ → ‖E w‖ ≤ Real.exp (K * (Real.sqrt ‖w‖ + 1)))
    (hinj : Function.Injective l) (zeros : ∀ w, E w = 0 ↔ ∃ j, w = l j)
    (simple : ∀ j, deriv E (l j) ≠ 0) (hsum : Summable (fun j => ‖l j‖⁻¹))
    (z : ℂ) : E z = ∏' j, (1 - z / l j) := by
  classical
  obtain ⟨K, hK, hgrowth⟩ := growth
  have root (j) := (zeros (l j)).mpr ⟨j, rfl⟩
  have hn (j) : l j ≠ 0 := by
    intro h
    simpa [h, h0] using root j
  obtain ⟨radii, indexSets, _, htop₀, inside₀, _, exhaust₀, mirror₀⟩ :=
    DiskProduct.exists_exhaustion l hn hsum
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htop₀.eventually_gt_atTop (1 : ℝ))
  let R (k : ℕ) := radii (k + N)
  let S (k : ℕ) := indexSets (k + N)
  have hshift := tendsto_add_atTop_nat N
  have hlarge (k : ℕ) : 1 < R k := hN (k + N) (Nat.le_add_left N k)
  have hR (k : ℕ) : 0 < R k := zero_lt_one.trans (hlarge k)
  have htop : Tendsto R atTop atTop := htop₀.comp hshift
  have inside (k : ℕ) (j : ι) : j ∈ S k ↔ ‖l j‖ < R k := inside₀ (k + N) j
  have disk (k : ℕ) := disk_removal E l (S k) (M := Real.exp (K * (Real.sqrt (R k) + 1)))
    (hR k) hE h0 hinj root simple
    (fun j hj => (inside k j).mp hj)
    (fun w hw he => by
      obtain ⟨j, rfl⟩ := (zeros w).mp he
      exact ⟨j, (inside k j).mpr hw, rfl⟩)
    (fun w hw => by rw [← hw]; exact hgrowth w (hw.symm ▸ (hlarge k).le))
  choose q analytic normalized nz bounded identity using disk
  let A (k : ℕ) := (K + 1) * (Real.sqrt (R k) + 1)
  have log_at (k : ℕ) (hk : ‖z‖ < R k / 2) :=
    DiskRigidity.exists_log_bound (hR k) (show 0 < A k by dsimp [A]; positivity)
      (analytic k).differentiableOn (fun w hw => nz k w (mem_ball_zero_iff.mp hw))
      (normalized k) (fun w hw => (bounded k w (mem_ball_zero_iff.mp hw)).trans_lt
        (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (lt_add_one K) (by positivity)))) hk
  let v (k : ℕ) := if hk : ‖z‖ < R k / 2 then (log_at k hk).choose else 0
  have hz : ∀ᶠ k in atTop, ‖z‖ < R k / 2 :=
    (htop.eventually_gt_atTop (2 * ‖z‖)).mono (fun k hk => by linarith)
  have he : (fun k => q k z) =ᶠ[atTop] (fun k => exp (v k)) := by
    filter_upwards [hz] with k hk
    simpa only [v, dif_pos hk] using (log_at k hk).choose_spec.1.symm
  have hboundLim : Tendsto (fun k => 2 * A k * ‖z‖ / (R k / 2 - ‖z‖)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (K + 1) / 2)).mul (log_bound_tendsto hR htop ‖z‖)
    rw [mul_zero] at h
    apply h.congr
    intro k
    dsimp [A]
    ring
  have hv : Tendsto v atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) _ hboundLim
    filter_upwards [hz] with k hk
    simpa only [v, dif_pos hk] using (log_at k hk).choose_spec.2
  have hq : Tendsto (fun k => q k z) atTop (𝓝 1) := by
    simpa only [Complex.exp_zero] using
      ((Complex.continuous_exp.tendsto 0).comp hv).congr' he.symm
  have hinv : Summable (fun j => (l j)⁻¹) := Summable.of_norm (by simpa using hsum)
  have hlog := Complex.summable_log_one_add_of_summable (hinv.mul_left (-z))
  have hp : Multipliable (fun j => 1 - z / l j) := by
    apply Complex.multipliable_of_summable_log
    simpa only [div_eq_mul_inv, neg_mul, ← sub_eq_add_neg] using hlog
  have left := hq.mul (hp.hasProd.comp (exhaust₀.comp hshift))
  have right := (tendsto_const_nhds (x := E z)).mul ((mirror₀ z).comp hshift)
  have same := left.congr (fun k => identity k z)
  simpa only [one_mul, mul_one] using (tendsto_nhds_unique right same)

end SuperZeta.Factorization
