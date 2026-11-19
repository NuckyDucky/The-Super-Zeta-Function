import SuperZeta.CoupledProduct
import SuperZeta.DiskGrowth
import SuperZeta.DiskProductLimit
import SuperZeta.DiskRemoval
import SuperZeta.DiskRigidity

/-! The determinant product over the full, signed-quartet spectrum at unit coupling.
Finite disk factorization and a sublinear logarithmic growth bound determine the
normalization of the infinite product at every complex argument. -/
namespace SuperZeta.Factorization
open Complex Filter Metric
open scoped Topology
noncomputable section

/-- A normalized entire function of the growth of the squared cosine determinant
is the canonical product over any complete injective listing of its simple zeros
with absolutely summable reciprocals. -/
theorem eq_tprod {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ)
    (hE : Differentiable ℂ E) (h0 : E 0 = 1)
    (growth : ∀ w, ‖E w‖ ≤ Real.exp (2*Real.sqrt ‖w‖) + ‖w‖)
    (hinj : Function.Injective l) (zeros : ∀ w, E w=0 ↔ ∃ j, w=l j)
    (simple : ∀ j, deriv E (l j) ≠ 0) (hsum : Summable (fun j => ‖l j‖⁻¹))
    (z : ℂ) : E z = ∏' j, (1-z/l j) := by
  classical
  have root (j) := (zeros (l j)).mpr ⟨j,rfl⟩
  have hn (j) : l j ≠ 0 := by
    intro h
    simpa [h,h0] using root j
  obtain ⟨R,S,hR,htop,inside,_,exhaust,mirror⟩ := DiskProduct.exists_exhaustion l hn hsum
  have disk (k : ℕ) := disk_removal E l (S k) (hR k) hE h0 hinj root simple
    (fun j hj => (inside k j).mp hj)
    (fun w hw he => by
      obtain ⟨j,rfl⟩ := (zeros w).mp he
      exact ⟨j,(inside k j).mpr hw,rfl⟩)
    (fun w hw => (growth w).trans_eq (by rw [hw]))
  choose q analytic normalized nz bounded identity using disk
  let A (k : ℕ) := 2*Real.sqrt (R k)+2
  have log_at (k : ℕ) (hk : ‖z‖ < R k/2) :=
    DiskRigidity.exists_log_bound (hR k) (show 0 < A k by dsimp [A]; positivity)
      (analytic k).differentiableOn (fun w hw => nz k w (mem_ball_zero_iff.mp hw))
      (normalized k) (fun w hw => (bounded k w (mem_ball_zero_iff.mp hw)).trans_lt (growth_lt (hR k))) hk
  let v (k : ℕ) := if hk : ‖z‖ < R k/2 then (log_at k hk).choose else 0
  have hz : ∀ᶠ k in atTop, ‖z‖ < R k/2 :=
    (htop.eventually_gt_atTop (2*‖z‖)).mono (fun k hk => by linarith)
  have he : (fun k => q k z) =ᶠ[atTop] (fun k => exp (v k)) := by
    filter_upwards [hz] with k hk
    simpa only [v,dif_pos hk] using (log_at k hk).choose_spec.1.symm
  have hv : Tendsto v atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) _ (log_bound_tendsto hR htop ‖z‖)
    filter_upwards [hz] with k hk
    simpa only [v,dif_pos hk,A] using (log_at k hk).choose_spec.2
  have hq : Tendsto (fun k => q k z) atTop (𝓝 1) := by
    simpa only [Complex.exp_zero] using
      ((Complex.continuous_exp.tendsto 0).comp hv).congr' he.symm
  have hinv : Summable (fun j => (l j)⁻¹) := Summable.of_norm (by simpa using hsum)
  have hlog := Complex.summable_log_one_add_of_summable (hinv.mul_left (-z))
  have hp : Multipliable (fun j => 1-z/l j) := by
    apply Complex.multipliable_of_summable_log
    simpa only [div_eq_mul_inv, neg_mul, ← sub_eq_add_neg] using hlog
  have left := hq.mul (hp.hasProd.comp exhaust)
  have right := (tendsto_const_nhds (x:=E z)).mul (mirror z)
  have same := left.congr (fun k => identity k z)
  simpa only [one_mul,mul_one] using (tendsto_nhds_unique right same)

end
end SuperZeta.Factorization

namespace SuperZeta.Ray
open Set Complex
noncomputable section

/-- Global equality of the determinant and the product over its classified squared roots. -/
theorem coupledDet_eq_tprod {d : ℝ}
    (hd : d ∈ Ioo 0 (Real.pi/2) ∧ d = Real.cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1)) (w : ℂ) :
    Spectrum.coupledDet w = ∏' j, (1-w/RootBounds.family d t j) := by
  have zeros (v : ℂ) := Spectrum.coupledDet_zero_iff_unique_index hd roots v
  have hinj := RootBounds.family_injective d roots
  apply Factorization.eq_tprod
    _ _ (fun v => (Spectrum.coupledDet_analytic v).differentiableAt)
    Spectrum.coupledDet_zero Spectrum.coupledDet_growth hinj
  · intro v
    rw [zeros]
    exact ⟨ExistsUnique.exists,fun ⟨i,hi⟩ =>
      ⟨i,hi,fun j hj => hinj (hj.symm.trans hi)⟩⟩
  · intro i
    apply Spectrum.coupledDet_simple
    exact (zeros _).mpr ⟨i,rfl,fun j hj => hinj hj.symm⟩
  · simpa [Real.rpow_neg (norm_nonneg _)] using (indexed_data (s:=1) hd.1.1 roots (by norm_num)).powers

/-- Mellin reconstruction directly from the actual squared roots. The only
inputs describe the Dottie root, the indexed levels and the convergence strip. -/
theorem root_series_reconstruction {d : ℝ}
    (hd : d ∈ Ioo 0 (Real.pi/2) ∧ d = Real.cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1))
    {s : ℂ} (hs : 1/2<s.re) (hu : s.re<1) :
    (∑' j, (RootBounds.family d t j)^(-s)) - Reference.entireCorrection 1 s =
      Spectrum.riemannFactor s * riemannZeta (2*s) := by
  apply reconstruction_from_ray_product hd.1.1 roots _ hs hu
  intro r hr
  simpa [neg_div] using (coupledDet_eq_tprod hd roots (-(r:ℂ))).symm.trans
    (Spectrum.coupledDet_on_ray hr.le)

end
end SuperZeta.Ray
