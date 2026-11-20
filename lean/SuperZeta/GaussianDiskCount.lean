import SuperZeta.GaussianEndpointParity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

/-! The reflected Gaussian disks. The trace estimate and the bounds on the smoothed
Dirichlet sums are inputs from the directed numerical certificates. -/

namespace SuperZeta.GaussianDiskCount

noncomputable section
open Metric Set
open scoped ComplexConjugate BigOperators Classical Topology

/-- Both centers use the Dottie height translated down by 1/512. -/
def rightCenter (T_D : ℝ) : ℂ := ⟨33 / 64, T_D - 1 / 512⟩
def leftCenter (T_D : ℝ) : ℂ := ⟨31 / 64, T_D - 1 / 512⟩
abbrev radius : ℝ := 15 / 1024

theorem reflect_center (T_D : ℝ) : 1 - conj (rightCenter T_D) = leftCenter T_D := by
  apply Complex.ext <;> norm_num [rightCenter, leftCenter]

theorem reflect_dist (z c : ℂ) : dist (1 - conj z) (1 - conj c) = dist z c := by
  simp only [dist_eq_norm]
  rw [show (1 - conj z) - (1 - conj c) = -conj (z - c) by
    rw [map_sub]; abel]
  rw [norm_neg, Complex.norm_conj]

theorem mem_right_iff_reflect_mem_left (T_D : ℝ) (z : ℂ) :
    z ∈ closedBall (rightCenter T_D) radius ↔
      1 - conj z ∈ closedBall (leftCenter T_D) radius := by
  simp only [mem_closedBall, ← reflect_center T_D, reflect_dist]

/-- The two closed disks stop 1/1024 short of the critical line on each side. -/
theorem disk_real_bounds (T_D : ℝ) (z : ℂ) :
    (z ∈ closedBall (rightCenter T_D) radius →
      513 / 1024 ≤ z.re ∧ z.re ≤ 543 / 1024) ∧
    (z ∈ closedBall (leftCenter T_D) radius →
      481 / 1024 ≤ z.re ∧ z.re ≤ 511 / 1024) := by
  have endpoints (c : ℂ) (hz : z ∈ closedBall c radius) :
      |z.re - c.re| ≤ radius :=
    (Complex.abs_re_le_norm (z - c)).trans (by simpa only [mem_closedBall, dist_eq_norm] using hz)
  constructor <;> intro hz
  · have h := abs_le.mp (endpoints _ hz)
    change -(15 / 1024 : ℝ) ≤ z.re - 33 / 64 ∧ z.re - 33 / 64 ≤ 15 / 1024 at h
    constructor <;> linarith
  · have h := abs_le.mp (endpoints _ hz)
    change -(15 / 1024 : ℝ) ≤ z.re - 31 / 64 ∧ z.re - 31 / 64 ≤ 15 / 1024 at h
    constructor <;> linarith

theorem disks_within_height_band (T_D : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (rightCenter T_D) radius ∨ z ∈ closedBall (leftCenter T_D) radius) :
    |z.im - (T_D - 1 / 512)| ≤ radius := by
  rcases hz with hz | hz
  · exact (Complex.abs_im_le_norm (z - rightCenter T_D)).trans
      (by simpa only [mem_closedBall, dist_eq_norm] using hz)
  · exact (Complex.abs_im_le_norm (z - leftCenter T_D)).trans
      (by simpa only [mem_closedBall, dist_eq_norm] using hz)

/-- Conjugating both the input and output of a holomorphic germ preserves analyticity.
Conjugating its difference quotient conjugates the derivative. -/
private theorem analytic_conj_conj {g : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c) :
    AnalyticAt ℂ (fun y => conj (g (conj y))) (conj c) := by
  have hcc : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (conj c)) (𝓝 c) := by
    simpa using (Complex.continuous_conj.continuousAt (x := conj c)).tendsto
  have hc0 : Filter.Tendsto (conj : ℂ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Complex.continuous_conj.continuousAt
        (x := (0:ℂ))).tendsto.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hcc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with y hy
  apply HasDerivAt.differentiableAt (f' := conj (deriv g (conj y)))
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    (hy.hasDerivAt.tendsto_slope_zero.comp hc0)
  simpa only [Function.comp_def, smul_eq_mul, map_mul, map_inv₀, map_sub, map_add,
    Complex.conj_conj] using h

/-- The functional equation preserves the actual analytic order. The sign from
reflecting the centered monomial is an invertible constant in the analytic cofactor. -/
theorem reflected_analytic_order {f : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f c) (hr : AnalyticAt ℂ f (1 - conj c))
    (hs : ∀ y, f (1 - conj y) = conj (f y)) (hn : hf.order = n) :
    hr.order = n := by
  obtain ⟨g, hg, hg₀, hfac⟩ := hf.order_eq_nat_iff.mp hn
  have ha : AnalyticAt ℂ (fun y : ℂ => 1 - y) (1 - c) := by fun_prop
  have hc : AnalyticAt ℂ g (1 - (1 - c)) := by simpa using hg
  have hg' := analytic_conj_conj (g := fun y : ℂ => g (1-y)) (hc.comp ha)
  simp only [map_sub, map_one] at hg'
  refine hr.order_eq_nat_iff.mpr ⟨fun y => (-1 : ℂ)^n * conj (g (1 - conj y)),
    analyticAt_const.mul hg', by simpa using hg₀, ?_⟩
  have hcont : Continuous (fun y : ℂ => 1 - conj y) := continuous_const.sub Complex.continuous_conj
  have ht : Filter.Tendsto (fun y : ℂ => 1 - conj y) (𝓝 (1 - conj c)) (𝓝 c) := by
    simpa using (hcont.continuousAt (x := 1 - conj c)).tendsto
  filter_upwards [ht.eventually hfac] with y hy
  calc
    f y = conj (f (1 - conj y)) := by rw [hs]; simp
    _ = _ := by
      rw [hy]
      simp only [smul_eq_mul, map_mul, map_pow, map_sub, map_one, Complex.conj_conj]
      rw [show 1 - y - conj c = (-1 : ℂ) * (y - (1 - conj c)) by ring, mul_pow]
      ring

/-- Reflection is a multiplicity-preserving bijection of the two disk inventories. -/
theorem equal_disk_counts (T_D : ℝ) (roots : Finset ℂ) (m : ℂ → ℕ)
    (href : ∀ z ∈ roots, 1 - conj z ∈ roots)
    (hm : ∀ z ∈ roots, m (1 - conj z) = m z) :
    (roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius)).sum m =
      (roots.filter (fun z => z ∈ closedBall (leftCenter T_D) radius)).sum m := by
  classical
  apply Finset.sum_nbij' (fun z : ℂ => 1 - conj z) (fun z : ℂ => 1 - conj z)
  · intro z hz
    obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨href z hmem, (mem_right_iff_reflect_mem_left T_D z).mp hdist⟩
  · intro z hz
    obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨href z hmem, (mem_right_iff_reflect_mem_left T_D _).mpr ?_⟩
    simpa using hdist
  · intro z _; simp
  · intro z _; simp
  · intro z hz; exact (hm z (Finset.mem_filter.mp hz).1).symm

/-- The explicit formula bounds the weight of a whole height band.
The lower bound on each unit of multiplicity first gives fifteen in the band,
then symmetry and the gap to the critical line give seven in each disk. -/
theorem disk_count_from_trace (T_D : ℝ) (roots : Finset ℂ) (m : ℂ → ℕ) (weight : ℂ → ℝ)
    (href : ∀ z ∈ roots, 1 - conj z ∈ roots)
    (hm : ∀ z ∈ roots, m (1 - conj z) = m z)
    (hmin : ∀ z ∈ roots, 5.481507 ≤ weight z)
    (hbudget : (∑ z ∈ roots, (m z : ℝ) * weight z) ≤ 87.057901) :
    roots.sum m ≤ 15 ∧
    (roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius)).sum m ≤ 7 ∧
    (roots.filter (fun z => z ∈ closedBall (leftCenter T_D) radius)).sum m ≤ 7 := by
  classical
  have lower : ((roots.sum m : ℕ) : ℝ) * 5.481507 ≤ 87.057901 := by
    push_cast
    rw [Finset.sum_mul]
    exact le_trans (Finset.sum_le_sum fun z hz =>
      mul_le_mul_of_nonneg_left (hmin z hz) (Nat.cast_nonneg _)) hbudget
  have band : roots.sum m ≤ 15 := by
    by_contra h
    have g : 16 ≤ roots.sum m := Nat.succ_le_of_lt (lt_of_not_ge h)
    have gr : (16 : ℝ) ≤ ((roots.sum m : ℕ) : ℝ) := by exact_mod_cast g
    linarith
  have subsetRight : roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius) ⊆
      roots.filter (fun z => 1 / 2 < z.re) := by
    intro z hz
    obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp hz
    have h := ((disk_real_bounds T_D z).1 hdist).1
    exact Finset.mem_filter.mpr ⟨hmem, by linarith⟩
  have leRight : (roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius)).sum m ≤
      (roots.filter (fun z => 1 / 2 < z.re)).sum m :=
    Finset.sum_le_sum_of_subset_of_nonneg subsetRight (f := m) (fun _ _ _ => Nat.zero_le _)
  have split := GaussianEndpointParity.reflected_total roots m href hm
  have right : (roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius)).sum m ≤ 7 := by
    omega
  exact ⟨band, right, (equal_disk_counts T_D roots m href hm) ▸ right⟩

/-- For an analytic function satisfying the Gaussian reflection equation, specify
the finite zero list by its geometric membership test and each multiplicity by
Mathlib's analytic order. The paired bounds then require only the trace inputs. -/
theorem analytic_disk_counts_from_trace (T_D : ℝ) {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hs : ∀ z, f (1 - conj z) = conj (f z))
    (roots : Finset ℂ) (m : ℂ → ℕ) (weight : ℂ → ℝ)
    (hlist : ∀ z, z ∈ roots ↔ 0 ≤ z.re ∧ z.re ≤ 1 ∧
      |z.im - (T_D - 1 / 512)| ≤ radius ∧ f z = 0)
    (hord : ∀ z ∈ roots, (hf z).order = m z)
    (hmin : ∀ z ∈ roots, 5.481507 ≤ weight z)
    (hbudget : (∑ z ∈ roots, (m z : ℝ) * weight z) ≤ 87.057901) :
    let right := (roots.filter (fun z => z ∈ closedBall (rightCenter T_D) radius)).sum m
    let left := (roots.filter (fun z => z ∈ closedBall (leftCenter T_D) radius)).sum m
    roots.sum m ≤ 15 ∧ right = left ∧ right ≤ 7 ∧ left ≤ 7 := by
  have href (z : ℂ) (hz : z ∈ roots) : 1 - conj z ∈ roots := by
    obtain ⟨h0, h1, ht, he⟩ := (hlist z).mp hz
    apply (hlist _).mpr
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im,
      Complex.one_im, Complex.conj_im, zero_sub, neg_neg, hs, he, map_zero]
    exact ⟨by linarith, by linarith, ht, trivial⟩
  have hm (z : ℂ) (hz : z ∈ roots) : m (1 - conj z) = m z := by
    have h := reflected_analytic_order (hf z) (hf _) hs (hord z hz)
    rw [hord _ (href z hz)] at h
    exact_mod_cast h
  obtain ⟨hl, hr, hl'⟩ := disk_count_from_trace T_D roots m weight href hm hmin hbudget
  exact ⟨hl, equal_disk_counts T_D roots m href hm, hr, hl'⟩

/-- A strictly negative real part on the circle clears the closed disk:
apply the maximum modulus principle to exp(f), whose norm is exp(Re f). -/
theorem zero_free_of_negative_boundary {c : ℂ} {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball c r))
    (hboundary : ∀ z ∈ sphere c r, (f z).re < 0) :
    ∀ z ∈ closedBall c r, f z ≠ 0 := by
  have he : DiffContOnCl ℂ (fun z => Complex.exp (f z)) (ball c r) :=
    ⟨Complex.differentiable_exp.comp_differentiableOn hf.differentiableOn,
     Complex.continuous_exp.comp_continuousOn hf.continuousOn⟩
  obtain ⟨b, hb, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    isBounded_ball ⟨c, mem_ball_self hr⟩ he
  rw [frontier_ball c hr.ne'] at hb
  intro z hz hzero
  have hz' : z ∈ closure (ball c r) := by simpa only [closure_ball c hr.ne'] using hz
  have bound : ‖Complex.exp (f z)‖ ≤ ‖Complex.exp (f b)‖ := hmax hz'
  rw [hzero, Complex.exp_zero, norm_one, Complex.norm_exp] at bound
  exact (not_le_of_gt (Real.exp_lt_one_iff.mpr (hboundary b hb))) bound

/-- Only an upper bound for the real part of the signed remainder is needed.
The positive bound on the remainder below is the open input in the Gaussian computation. -/
theorem zero_free_of_signed_remainder (T_D : ℝ) {f partialSum : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball (rightCenter T_D) radius))
    (hp : ∀ z ∈ sphere (rightCenter T_D) radius, (partialSum z).re ≤ -(7.6098 / 10^29))
    (hr : ∀ z ∈ sphere (rightCenter T_D) radius, (f z - partialSum z).re < 7.6098 / 10^29) :
    ∀ z ∈ closedBall (rightCenter T_D) radius, f z ≠ 0 := by
  apply zero_free_of_negative_boundary (by norm_num [radius]) hf
  intro z hz
  have h := hr z hz
  rw [Complex.sub_re] at h
  linarith [hp z hz]

/-- Reflection carries any putative zero in the left disk to the right disk.
One signed boundary estimate would therefore exclude zeros in both. -/
theorem zero_free_in_both_of_signed_remainder (T_D : ℝ) {f partialSum : ℂ → ℂ}
    (hs : ∀ z, f (1 - conj z) = conj (f z))
    (hf : DiffContOnCl ℂ f (ball (rightCenter T_D) radius))
    (hp : ∀ z ∈ sphere (rightCenter T_D) radius, (partialSum z).re ≤ -(7.6098 / 10^29))
    (hr : ∀ z ∈ sphere (rightCenter T_D) radius, (f z - partialSum z).re < 7.6098 / 10^29)
    (z : ℂ) (hz : z ∈ closedBall (rightCenter T_D) radius ∨ z ∈ closedBall (leftCenter T_D) radius) :
    f z ≠ 0 := by
  have hright := zero_free_of_signed_remainder T_D hf hp hr
  rcases hz with h | h
  · exact hright z h
  · have hn := hright (1 - conj z) ((mem_right_iff_reflect_mem_left T_D _).mpr (by simpa using h))
    simpa only [hs, ne_eq, map_eq_zero] using hn

end
end SuperZeta.GaussianDiskCount
