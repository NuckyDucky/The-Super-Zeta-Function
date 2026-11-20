import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Endpoint signs of a real analytic function and multiplicities of its zeros. -/

namespace SuperZeta.GaussianEndpointParity

open Set Filter
open scoped Topology BigOperators

/-- Removing a zero of known analytic order gives an analytic cofactor on the
interval. The construction fills in the quotient at the removed zero using its germ. -/
private theorem remove_zero {f : ℝ → ℝ} {D : Set ℝ} {r : ℝ} {m : ℕ}
    (hf : ∀ x ∈ D, AnalyticAt ℝ f x) (hr : r ∈ D)
    (hm : (hf r hr).order = m) :
    ∃ g : ℝ → ℝ, (∀ x ∈ D, AnalyticAt ℝ g x) ∧ g r ≠ 0 ∧
      (∀ x, f x = (x-r)^m * g x) := by
  classical
  obtain ⟨u, hu, hu₀, he⟩ := (hf r hr).order_eq_nat_iff.mp hm
  let g (x : ℝ) := if x = r then u r else f x / (x-r)^m
  have hgerm : u =ᶠ[𝓝 r] g := by
    filter_upwards [he] with x hx
    by_cases e : x = r
    · subst x
      simp [g]
    · simp [g, e, hx, smul_eq_mul, pow_ne_zero m (sub_ne_zero.mpr e)]
  refine ⟨g, ?_, by simpa [g] using hu₀, ?_⟩
  · intro x hx
    by_cases e : x = r
    · subst x
      exact hu.congr hgerm
    · have hq : AnalyticAt ℝ (fun y => f y / (y-r)^m) x :=
        (hf x hx).div (by fun_prop) (pow_ne_zero m (sub_ne_zero.mpr e))
      apply hq.congr
      filter_upwards [IsOpen.mem_nhds isOpen_ne e] with y hy
      simp [g, hy]
  · intro x
    by_cases e : x = r
    · subst x
      simpa [g, smul_eq_mul] using he.self_of_nhds
    · simp [g, e, mul_comm ((x-r)^m), pow_ne_zero m (sub_ne_zero.mpr e)]

private theorem endpoint_product_pos {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hn : ∀ x ∈ Icc a b, g x ≠ 0) :
    0 < g a * g b := by
  have ha := hn a (left_mem_Icc.mpr hab.le)
  have hb := hn b (right_mem_Icc.mpr hab.le)
  by_contra! h
  have hop := mul_neg_iff.mp (lt_of_le_of_ne h (mul_ne_zero ha hb))
  have hz : (0 : ℝ) ∈ g '' Icc a b := by
    rcases hop with h | h
    · exact intermediate_value_Icc' hab.le hg ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hg ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, he⟩ := hz
  exact hn x hx he

/-- The sign-corrected product of the endpoint values is strictly positive.
The finite set lists all zeros on the closed interval, puts each strictly inside,
and assigns it its actual Mathlib analytic order. -/
theorem signed_endpoint_product_pos {a b : ℝ} (hab : a < b) (roots : Finset ℝ)
    (m : ℝ → ℕ) (f : ℝ → ℝ) (hf : ∀ x ∈ Icc a b, AnalyticAt ℝ f x)
    (hi : ∀ r ∈ roots, r ∈ Ioo a b)
    (hlist : ∀ x ∈ Icc a b, f x = 0 → x ∈ roots)
    (hord : ∀ r (hr : r ∈ roots), (hf r (Ioo_subset_Icc_self (hi r hr))).order = m r) :
    0 < (-1 : ℝ) ^ (∑ r ∈ roots, m r) * (f a * f b) := by
  classical
  induction roots using Finset.induction_on generalizing f with
  | empty =>
    simpa using endpoint_product_pos hab (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx h => by simpa using hlist x hx h)
  | @insert c s hcs ih =>
    have hc : c ∈ Ioo a b := hi c (Finset.mem_insert_self _ _)
    obtain ⟨g, hg, hgc, hfg⟩ := remove_zero hf (Ioo_subset_Icc_self hc)
      (hord c (Finset.mem_insert_self _ _))
    have hs : ∀ x ∈ s, x ∈ Ioo a b := fun x hx => hi x (Finset.mem_insert_of_mem hx)
    have hlist' (x : ℝ) (hx : x ∈ Icc a b) (hz : g x = 0) : x ∈ s := by
      have hh := hlist x hx (by rw [hfg, hz, mul_zero])
      rcases Finset.mem_insert.mp hh with e | h
      · subst x
        exact (hgc hz).elim
      · exact h
    have hord' (x : ℝ) (hx : x ∈ s) : (hg x (Ioo_subset_Icc_self (hs x hx))).order = m x := by
      have hxc : x ≠ c := fun e => hcs (e ▸ hx)
      have hd : AnalyticAt ℝ (fun t : ℝ => (t-c)^m c) x := by fun_prop
      have hd0 := hd.order_eq_zero_iff.mpr (pow_ne_zero _ (sub_ne_zero.mpr hxc))
      have hprod := hd.order_mul (hg x (Ioo_subset_Icc_self (hs x hx)))
      have hordprod := (hd.mul (hg x (Ioo_subset_Icc_self (hs x hx)))).order_congr
        (Filter.Eventually.of_forall (fun t => (hfg t).symm))
      rw [hd0, zero_add] at hprod
      exact hprod.symm.trans (hordprod.symm.trans (hord x (Finset.mem_insert_of_mem hx)))
    have hind := ih g hg hs hlist' hord'
    have hmid : 0 < (-(a-c)*(b-c)) ^ (m c) := pow_pos (mul_pos (neg_pos.mpr (sub_neg.mpr hc.1))
      (sub_pos.mpr hc.2)) _
    rw [Finset.sum_insert hcs, pow_add, hfg a, hfg b]
    convert mul_pos hmid hind using 1
    simp only [← neg_one_mul (a-c), mul_pow]
    ring

/-- Opposite endpoint signs are equivalent to odd total multiplicity. Equal
nonzero signs are equivalent to even total multiplicity. -/
theorem endpoint_parity {a b : ℝ} (hab : a < b) (roots : Finset ℝ)
    (m : ℝ → ℕ) (f : ℝ → ℝ) (hf : ∀ x ∈ Icc a b, AnalyticAt ℝ f x)
    (hi : ∀ r ∈ roots, r ∈ Ioo a b)
    (hlist : ∀ x ∈ Icc a b, f x = 0 → x ∈ roots)
    (hord : ∀ r (hr : r ∈ roots), (hf r (Ioo_subset_Icc_self (hi r hr))).order = m r) :
    (f a * f b < 0 ↔ Odd (∑ r ∈ roots, m r)) ∧
    (0 < f a * f b ↔ Even (∑ r ∈ roots, m r)) := by
  have h := signed_endpoint_product_pos hab roots m f hf hi hlist hord
  rcases Nat.even_or_odd (∑ r ∈ roots, m r) with he | ho
  · rw [he.neg_one_pow, one_mul] at h
    simp [h, he, Nat.not_odd_iff_even.mpr he, not_lt.mpr h.le]
  · rw [ho.neg_one_pow, neg_one_mul, neg_pos] at h
    simp [h, ho, Nat.not_even_iff_odd.mpr ho, not_lt.mpr h.le]

/-- The zeros on a bounded interval form a finite set whenever the analytic
function is nonzero at its left endpoint. An infinite set would have an
accumulation point, so the analytic identity theorem would force a zero there
and at the left endpoint as well. -/
theorem finite_interior_zeros {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (ha : f a ≠ 0) :
    {x : ℝ | x ∈ Ioo a b ∧ f x = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hx, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact
    hinf isCompact_Icc (fun _ h => Ioo_subset_Icc_self h.1)
  have hfreq : ∃ᶠ t in 𝓝[≠] x, f t = 0 := by
    apply frequently_nhdsWithin_iff.mpr
    exact (accPt_iff_frequently.mp hacc).mono fun t ht => ⟨ht.2.2, ht.1⟩
  exact ha ((hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Icc hx hfreq)
    (left_mem_Icc.mpr hab))

private noncomputable def multiplicity (f : ℝ → ℝ) (x : ℝ) : ℕ := by
  classical
  exact if h : AnalyticAt ℝ f x then h.order.toNat else 0

/-- Sum of the actual orders of the zeros strictly between the two heights. -/
noncomputable def interiorZeroCount {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (ha : f a ≠ 0) : ℕ :=
  (finite_interior_zeros hab hf ha).toFinset.sum (multiplicity f)

/-- The sign-parity test with the complete zero inventory and its finite
multiplicities derived from analyticity and nonvanishing endpoints. -/
theorem analytic_endpoint_parity {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (ha : f a ≠ 0) (hb : f b ≠ 0) :
    (f a * f b < 0 ↔ Odd (interiorZeroCount hab.le hf ha)) ∧
    (0 < f a * f b ↔ Even (interiorZeroCount hab.le hf ha)) := by
  classical
  let S := (finite_interior_zeros hab.le hf ha).toFinset
  have hmem (x : ℝ) : x ∈ S ↔ x ∈ Ioo a b ∧ f x = 0 := Set.Finite.mem_toFinset _
  apply endpoint_parity hab S (multiplicity f) f hf (fun r hr => ((hmem r).mp hr).1)
  · intro x hx hz
    apply (hmem x).mpr
    exact ⟨⟨lt_of_le_of_ne hx.1 (fun e => ha (e ▸ hz)),
      lt_of_le_of_ne hx.2 (fun e => hb (e ▸ hz))⟩, hz⟩
  · intro x hx
    have hxin := Ioo_subset_Icc_self ((hmem x).mp hx).1
    have hfx := hf x hxin
    have hfin : hfx.order ≠ ⊤ := by
      intro htop
      exact ha ((hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc
        hxin (hfx.order_eq_top_iff.mp htop)) (left_mem_Icc.mpr hab.le))
    simpa [multiplicity, hfx] using (ENat.coe_toNat hfin).symm

/-- At a real target different from both endpoint readings, the number of
preimages on the open interval is odd exactly between the two readings. -/
theorem shifted_odd_target_interval {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (v : ℝ) (ha : f a ≠ v) (hb : f b ≠ v) :
    Odd (interiorZeroCount hab.le (f := fun x => f x - v)
      (fun x hx => (hf x hx).sub analyticAt_const) (sub_ne_zero.mpr ha)) ↔
      v ∈ Ioo (min (f a) (f b)) (max (f a) (f b)) := by
  have h := (analytic_endpoint_parity hab (f := fun x => f x - v)
    (fun x hx => (hf x hx).sub analyticAt_const)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)).1.symm
  refine h.trans ?_
  change (f a - v) * (f b - v) < 0 ↔ _
  rcases le_total (f a) (f b) with h | h
  · rw [min_eq_left h, max_eq_right h, mem_Ioo, mul_neg_iff]
    constructor
    · rintro (⟨ha', hb'⟩ | ⟨ha', hb'⟩) <;> constructor <;> linarith
    · rintro ⟨ha', hb'⟩
      exact Or.inr ⟨by linarith, by linarith⟩
  · rw [min_eq_right h, max_eq_left h, mem_Ioo, mul_neg_iff]
    constructor
    · rintro (⟨ha', hb'⟩ | ⟨ha', hb'⟩) <;> constructor <;> linarith
    · rintro ⟨ha', hb'⟩
      exact Or.inl ⟨by linarith, by linarith⟩

open scoped ComplexConjugate

/-- Reflection at the critical line preserves height. In a finite symmetric
root family the total multiplicity is the line count plus twice the count
strictly to its right. -/
theorem reflected_total (roots : Finset ℂ) (m : ℂ → ℕ)
    (href : ∀ z ∈ roots, 1 - conj z ∈ roots)
    (hm : ∀ z ∈ roots, m (1 - conj z) = m z) :
    roots.sum m = (roots.filter (fun z => z.re = 1 / 2)).sum m +
      2 * (roots.filter (fun z => 1 / 2 < z.re)).sum m := by
  classical
  let left := roots.filter (fun z => z.re < 1 / 2)
  let right := roots.filter (fun z => 1 / 2 < z.re)
  let line := roots.filter (fun z => z.re = 1 / 2)
  have hpair : left.sum m = right.sum m := by
    apply Finset.sum_nbij' (fun z : ℂ => 1 - conj z) (fun z : ℂ => 1 - conj z)
    · intro z hz
      obtain ⟨hz₁,hz₂⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨href _ hz₁, ?_⟩
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · intro z hz
      obtain ⟨hz₁,hz₂⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨href _ hz₁, ?_⟩
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · intro z _; simp
    · intro z _; simp
    · intro z hz; exact (hm z (Finset.mem_filter.mp hz).1).symm
  have hsplit : roots.sum m = line.sum m + left.sum m + right.sum m := by
    dsimp only [line, left, right]
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rcases lt_trichotomy z.re (1 / 2) with h | h | h
    · simp only [h, h.ne, not_lt.mpr h.le, if_true, if_false, zero_add, add_zero]
    · simp [h]
    · simp only [h, h.ne', not_lt.mpr h.le, if_true, if_false, zero_add, add_zero]
  change roots.sum m = line.sum m + 2 * right.sum m
  rw [hsplit, hpair]
  omega

/-- A full-strip count is odd exactly when its critical-line count is odd. -/
theorem reflected_odd_iff (roots : Finset ℂ) (m : ℂ → ℕ)
    (href : ∀ z ∈ roots, 1 - conj z ∈ roots)
    (hm : ∀ z ∈ roots, m (1 - conj z) = m z) :
    Odd (roots.sum m) ↔ Odd ((roots.filter (fun z => z.re = 1 / 2)).sum m) := by
  rw [reflected_total roots m href hm, Nat.odd_add]
  simp

end SuperZeta.GaussianEndpointParity
