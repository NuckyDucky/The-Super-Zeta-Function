import GaussianSquaredRamp
import Mathlib.Algebra.BigOperators.Intervals

/-! Kominers's strict row triangle and its floor-weighted prime count. -/

namespace AlpogeSuperZeta

open Finset

noncomputable section

def frobeniusTriangleRows (k t : ℝ) : ℕ :=
  ∑ s ∈ range ⌈t / k⌉₊, ⌈t - k * (s : ℝ)⌉₊

theorem frobeniusTriangleRows_eq_zero {k t : ℝ} (hk : 0 < k) (ht : t ≤ 0) :
    frobeniusTriangleRows k t = 0 := by
  rw [frobeniusTriangleRows, Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg ht hk.le)]
  simp

theorem frobeniusTriangleRows_error {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    0 ≤ (frobeniusTriangleRows k t : ℝ) - t ^ 2 / (2 * k) ∧
      (frobeniusTriangleRows k t : ℝ) - t ^ 2 / (2 * k) ≤ t + t / k + 1 := by
  let n : ℕ := ⌈t / k⌉₊
  let q : ℝ := t / k
  let f (s : ℕ) : ℝ := t - k * (s : ℝ)
  let S : ℝ := ∑ s ∈ range n, f s
  have hq : 0 < q := div_pos ht hk
  have hn : 1 ≤ n := Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using hq)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hgap0 : 0 ≤ (n : ℝ) - q := sub_nonneg.mpr (Nat.le_ceil q)
  have hgap1 : (n : ℝ) - q < 1 := by
    have h := Nat.ceil_lt_add_one hq.le
    change (n : ℝ) < q + 1 at h
    linarith
  have hf (s : ℕ) (hs : s ∈ range n) : 0 ≤ f s := by
    have h : (s : ℝ) < t / k := Nat.lt_ceil.mp (mem_range.mp hs)
    dsimp [f]
    linarith [(lt_div_iff₀ hk).mp h]
  have hS₀ : S ≤ (frobeniusTriangleRows k t : ℝ) := by
    unfold frobeniusTriangleRows
    rw [Nat.cast_sum]
    exact sum_le_sum fun s _ => Nat.le_ceil (f s)
  have hS₁ : (frobeniusTriangleRows k t : ℝ) ≤ S + n := by
    unfold frobeniusTriangleRows
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ s ∈ range n, (f s + 1) :=
        sum_le_sum fun s hs => (Nat.ceil_lt_add_one (hf s hs)).le
      _ = S + n := by simp [S, sum_add_distrib]
  have hsum : ∑ s ∈ range n, (s : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) (sum_range_id_mul_two n)
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_sub hn, Nat.cast_one] at h
    linarith
  have hS : S - t ^ 2 / (2 * k) = (k / 2) * ((n : ℝ) - ((n : ℝ) - q) ^ 2) := by
    dsimp [S, f, q]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, hsum]
    field_simp
    ring
  have hA : 0 ≤ (n : ℝ) - ((n : ℝ) - q) ^ 2 := by
    nlinarith [mul_nonneg hgap0 (sub_nonneg.mpr hgap1.le)]
  have hB : (n : ℝ) - ((n : ℝ) - q) ^ 2 ≤ 2 * q := by
    nlinarith [sq_nonneg ((n : ℝ) - q - 1)]
  have hl : 0 ≤ S - t ^ 2 / (2 * k) := by rw [hS]; exact mul_nonneg (by positivity) hA
  have hu : S - t ^ 2 / (2 * k) ≤ t := by
    rw [hS]
    calc
      _ ≤ (k / 2) * (2 * q) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = t := by dsimp [q]; field_simp
  have hceil : (n : ℝ) < t / k + 1 := Nat.ceil_lt_add_one hq.le
  constructor <;> linarith

def frobeniusTriangleDivisibility (X k : ℝ) (p : ℕ) : ℕ :=
  ∑ s ∈ range ⌈X / k⌉₊, ∑ r ∈ range ⌈X - k * (s : ℝ)⌉₊, r / p

private theorem sum_div_by_multiples {p N M : ℕ} (hp : 0 < p)
    (hM : ∀ r ∈ range N, r / p ≤ M) :
    (∑ r ∈ range N, r / p) = ∑ m ∈ range M, (N - (m + 1) * p) := by
  classical
  have hRow (r : ℕ) (hr : r ∈ range N) :
      r / p = ∑ m ∈ range M, (if (m + 1) * p ≤ r then 1 else 0 : ℕ) := by
    simp_rw [← Nat.le_div_iff_mul_le hp, Nat.succ_le_iff]
    rw [← sum_filter]
    have hf : (range M).filter (fun m => m < r / p) = range (r / p) := by
      ext m
      simp only [mem_filter, mem_range]
      exact ⟨And.right, fun h => ⟨h.trans_le (hM r hr), h⟩⟩
    rw [hf]
    simp
  have hCol (m : ℕ) :
      (∑ r ∈ range N, (if (m + 1) * p ≤ r then 1 else 0 : ℕ)) = N - (m + 1) * p := by
    rw [← sum_filter]
    have hf : (range N).filter (fun r => (m + 1) * p ≤ r) = Ico ((m + 1) * p) N := by
      ext r
      simp only [mem_filter, mem_range, mem_Ico]
      exact and_comm
    rw [hf]
    simp
  calc
    _ = ∑ r ∈ range N, ∑ m ∈ range M, (if (m + 1) * p ≤ r then 1 else 0 : ℕ) :=
      sum_congr rfl hRow
    _ = ∑ m ∈ range M, ∑ r ∈ range N, (if (m + 1) * p ≤ r then 1 else 0 : ℕ) := sum_comm
    _ = _ := sum_congr rfl fun m _ => hCol m

/-- Reindex the floor in each row by the positive multiples of p. -/
theorem frobeniusTriangleDivisibility_eq_sum {X k : ℝ} (hk : 0 < k) {p : ℕ} (hp : 0 < p) :
    frobeniusTriangleDivisibility X k p =
      ∑ m ∈ range ⌈X⌉₊, frobeniusTriangleRows k (X - (((m + 1) * p : ℕ) : ℝ)) := by
  unfold frobeniusTriangleDivisibility
  calc
    _ = ∑ s ∈ range ⌈X / k⌉₊, ∑ m ∈ range ⌈X⌉₊, (⌈X - k * (s : ℝ)⌉₊ - (m + 1) * p) := by
      apply sum_congr rfl
      intro s _
      apply sum_div_by_multiples hp
      intro r hr
      exact (Nat.div_le_self _ _).trans ((mem_range.mp hr).le.trans
        (Nat.ceil_le_ceil (sub_le_self _ (mul_nonneg hk.le (Nat.cast_nonneg _)))))
    _ = ∑ m ∈ range ⌈X⌉₊, ∑ s ∈ range ⌈X / k⌉₊, (⌈X - k * (s : ℝ)⌉₊ - (m + 1) * p) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro m _
      let d := (m + 1) * p
      let t := X - (d : ℝ)
      have htd : t ≤ X := sub_le_self _ (Nat.cast_nonneg _)
      have hCeil : ⌈t / k⌉₊ ≤ ⌈X / k⌉₊ :=
        Nat.ceil_le_ceil (div_le_div_of_nonneg_right htd hk.le)
      change (∑ s ∈ range ⌈X / k⌉₊, (⌈X - k * (s : ℝ)⌉₊ - d)) = frobeniusTriangleRows k t
      simp_rw [← Nat.ceil_sub_natCast, show ∀ y : ℝ, X - y - (d : ℝ) = t - y from
        fun y => by dsimp [t]; ring, frobeniusTriangleRows]
      symm
      apply sum_subset (range_mono hCeil)
      intro s _ hs
      apply Nat.ceil_eq_zero.mpr
      have hb : ⌈t / k⌉₊ ≤ s := le_of_not_gt (fun h => hs (mem_range.mpr h))
      have hdiv : t / k ≤ (s : ℝ) := Nat.ceil_le.mp hb
      linarith [(div_le_iff₀ hk).mp hdiv]

theorem frobeniusTriangleDivisibility_error {X k : ℝ} (hX : 1 ≤ X) (hk : 0 < k)
    {p : ℕ} (hp : 0 < p) :
    let D := (2 * k / X ^ 2) * (frobeniusTriangleDivisibility X k p : ℝ) -
      ∑ m ∈ range ⌈X⌉₊, squaredRampWeight X ((m + 1) * p)
    0 ≤ D ∧ D ≤ (2 * k / X ^ 2) * (X + X / k + 1) * (↑(⌈X / (p : ℝ)⌉₊ - 1) : ℝ) := by
  let c : ℝ := 2 * k / X ^ 2
  let B : ℝ := c * (X + X / k + 1)
  let N : ℕ := ⌈X⌉₊
  let Q : ℕ := ⌈X / (p : ℝ)⌉₊ - 1
  have hx : 0 < X := one_pos.trans_le hX
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  let d (m : ℕ) : ℝ := c * (frobeniusTriangleRows k (X - (((m + 1) * p : ℕ) : ℝ)) : ℝ) -
    squaredRampWeight X ((m + 1) * p)
  have h (m : ℕ) :
      0 ≤ d m ∧ d m ≤ if ((((m + 1) * p : ℕ) : ℝ) < X) then B else 0 := by
    by_cases hm : ((((m + 1) * p : ℕ) : ℝ) < X)
    · let t := X - (((m + 1) * p : ℕ) : ℝ)
      have ht : 0 < t := sub_pos.mpr hm
      have htX : t ≤ X := sub_le_self _ (Nat.cast_nonneg _)
      have heq : c * (t ^ 2 / (2 * k)) = squaredRampWeight X ((m + 1) * p) := by
        rw [squaredRampWeight, if_pos hm]
        dsimp [t, c]
        field_simp
      have hlim := frobeniusTriangleRows_error hk ht
      have hdiv := div_le_div_of_nonneg_right htX hk.le
      simp only [if_pos hm, d, ← heq, ← mul_sub]
      exact ⟨mul_nonneg hc hlim.1, mul_le_mul_of_nonneg_left (by linarith [hlim.2]) hc⟩
    · have hz := frobeniusTriangleRows_eq_zero hk (sub_nonpos.mpr (le_of_not_gt hm))
      have hd : d m = 0 := by
        dsimp [d]
        rw [hz, squaredRampWeight, if_neg hm]
        simp
      rw [hd, if_neg hm]
      exact ⟨le_rfl, le_rfl⟩
  have hQN : Q ≤ N := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hXdiv : X / (p : ℝ) ≤ X := by
      apply (div_le_iff₀ hp').mpr
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hp1)]
    exact (Nat.sub_le _ _).trans (Nat.ceil_le_ceil hXdiv)
  have hmem (m : ℕ) : (((m + 1) * p : ℕ) : ℝ) < X ↔ m < Q := by
    change (((m + 1) * p : ℕ) : ℝ) < X ↔ m < ⌈X / (p : ℝ)⌉₊ - 1
    rw [Nat.cast_mul, ← lt_div_iff₀ hp', ← Nat.lt_ceil]
    omega
  change 0 ≤ c * (frobeniusTriangleDivisibility X k p : ℝ) -
    ∑ m ∈ range N, squaredRampWeight X ((m + 1) * p) ∧ _ ≤ B * (Q : ℝ)
  rw [frobeniusTriangleDivisibility_eq_sum hk hp, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  change 0 ≤ ∑ m ∈ range N, d m ∧ (∑ m ∈ range N, d m) ≤ B * (Q : ℝ)
  refine ⟨sum_nonneg (fun m _ => (h m).1), ?_⟩
  calc
    _ ≤ ∑ m ∈ range N, (if m < Q then B else 0) :=
      sum_le_sum fun m _ => by simpa only [hmem m] using (h m).2
    _ = _ := by
      rw [← sum_filter]
      have hf : (range N).filter (fun m => m < Q) = range Q := by
        ext m
        simp only [mem_filter, mem_range]
        exact ⟨And.right, fun hm => ⟨hm.trans_le hQN, hm⟩⟩
      rw [hf, sum_const, card_range, nsmul_eq_mul, mul_comm]

#print axioms frobeniusTriangleRows_error
#print axioms frobeniusTriangleDivisibility_eq_sum
#print axioms frobeniusTriangleDivisibility_error

end
end AlpogeSuperZeta
