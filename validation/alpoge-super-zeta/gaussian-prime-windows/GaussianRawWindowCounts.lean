import GaussianDivisorWindow
import GaussianCommonDivisorPowers

/-! Group the finite window by its integer address before applying any
Möbius inversion. Each marked Gaussian prime is read by its containment tests. -/

namespace AlpogeSuperZeta

open Finset QuarticModel
open scoped Classical

noncomputable section

/-- The signed value at an original integer index includes every
occurrence whose address divides that index. -/
def archivedGaussianRawIndexCoefficient (n : ℕ) : ℝ :=
  ∑' i : GaussianIndexFamily, if gaussianIndexAddress i ∣ n then gaussianIndexCoefficient i else 0

private theorem divisorWindow_fiber {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) {n : ℕ} (hn : 0 < n) (i : ι) :
    (∑' m : ℕ, if divisorWindowIndex N (i, m) = n then b i else 0) =
      if N i ∣ n then b i else 0 := by
  by_cases h : N i ∣ n
  · obtain ⟨k, hk⟩ := h
    have hk₀ : 0 < k := by
      cases k with
      | zero => simp at hk; omega
      | succ k => omega
    have he : divisorWindowIndex N (i, k - 1) = n := by
      rw [divisorWindowIndex, Nat.sub_add_cancel hk₀, ← hk]
    rw [if_pos (hk ▸ dvd_mul_right (N i) k), tsum_eq_single (k - 1)]
    · rw [if_pos he]
    · intro m hm
      apply if_neg
      intro hm'
      have hc : N i * (m + 1) = N i * k := hm'.trans hk
      have hk' := Nat.eq_of_mul_eq_mul_left (hN i) hc
      exact hm (by omega)
  · rw [if_neg h]
    have he (m : ℕ) : (if divisorWindowIndex N (i, m) = n then b i else 0) = 0 :=
      if_neg (fun hm => h ⟨m + 1, hm.symm⟩)
    simp only [he, tsum_zero]

private theorem divisor_index_fiber_summable {n : ℕ} (hn : 0 < n) :
    Summable (fun p : GaussianIndexFamily × ℕ =>
      if divisorWindowIndex gaussianIndexAddress p = n then gaussianIndexCoefficient p.1 else 0) := by
  have hs := divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress
    (a := 2) (by norm_num) (gaussianIndexFamily_summable (by norm_num))
  apply Summable.of_abs
  refine (hs.mul_left ((n : ℝ) ^ (2 : ℝ))).of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_)
  split_ifs with h
  · rw [h, mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'
  · simp only [abs_zero]
    positivity

private theorem sum_divisor_index_fiber {n : ℕ} (hn : 0 < n) :
    (∑' p : GaussianIndexFamily × ℕ,
      if divisorWindowIndex gaussianIndexAddress p = n then gaussianIndexCoefficient p.1 else 0) =
      archivedGaussianRawIndexCoefficient n := by
  have h := divisor_index_fiber_summable hn
  have hf (i : GaussianIndexFamily) := h.comp_injective
    (show Function.Injective (fun m : ℕ => (i, m)) from fun _ _ he => congrArg Prod.snd he)
  rw [h.tsum_prod' hf]
  exact tsum_congr fun i => divisorWindow_fiber _ _ gaussianIndexAddress_pos hn i

/-- The original window sums one reading at each integer in
`[x/2,x)`. Several marked contributions at that address all count. -/
theorem archivedGaussianRawWindow_finite {x : ℝ} (hx : 1 ≤ x) :
    archivedGaussianRawWindow x =
      ∑ n ∈ (range (⌊x⌋₊ + 1)).filter (fun n : ℕ => 0 < n ∧ (n : ℝ) < x ∧ x ≤ 2 * n),
        archivedGaussianRawIndexCoefficient n := by
  let W := (range (⌊x⌋₊ + 1)).filter (fun n : ℕ => 0 < n ∧ (n : ℝ) < x ∧ x ≤ 2 * n)
  let g (n : ℕ) (p : GaussianIndexFamily × ℕ) : ℝ :=
    if divisorWindowIndex gaussianIndexAddress p = n then gaussianIndexCoefficient p.1 else 0
  have hh (n : ℕ) (hn : n ∈ W) : Summable (g n) :=
    divisor_index_fiber_summable (mem_filter.mp hn).2.1
  calc
    _ = ∑' p : GaussianIndexFamily × ℕ, ∑ n ∈ W, g n p := by
      unfold archivedGaussianRawWindow indexedCutoffSum
      apply tsum_congr
      intro p
      let k := divisorWindowIndex gaussianIndexAddress p
      have hk : 0 < k := divisorWindowIndex_pos gaussianIndexAddress_pos p
      have he : k ∈ W ↔ (k : ℝ) < x ∧ x ≤ 2 * k := by
        refine ⟨fun h => (mem_filter.mp h).2.2, fun h => ?_⟩
        have hfloor : k ≤ ⌊x⌋₊ := (Nat.le_floor_iff (zero_le_one.trans hx)).mpr h.1.le
        exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hfloor), hk, h⟩
      change gaussianIndexCoefficient p.1 * IndexedCutoff.window.weight x k = _
      simp only [g, IndexedCutoff.weight, ← he, mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq]
    _ = ∑ n ∈ W, ∑' p : GaussianIndexFamily × ℕ, g n p :=
      Summable.tsum_finsetSum (s := W) hh
    _ = _ := sum_congr rfl fun n hn => sum_divisor_index_fiber (mem_filter.mp hn).2.1

/-- The weighted divisor counts at one rational prime already occur in the
original common divisor, with each of its marked primes read separately. -/
theorem gaussianIndex_weighted_containment_at_prime {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : p.Coprime 26509772707289) (B : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ I ∈ gaussianPrimesAbove p, Real.log I.absNorm *
      (∑ j ∈ range B, if gaussianCommonDivisorIdeal n ≤ I ^ (j + 1) then (1 : ℝ) else 0)) =
      archivedInertIndexWeight p 1 *
        (∑ j ∈ range B, if (p + 1) * p ^ j ∣ n then (1 : ℝ) else 0) +
      archivedInertIndexWeight p 2 *
        (∑ j ∈ range B, if (p ^ 2 + 1) * p ^ j ∣ n then (1 : ℝ) else 0) := by
  have hgood : archivedGoodIndexPrime p := ⟨Fact.out, hp, hD⟩
  simp only [archivedInertIndexWeight, if_pos hgood, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun I hi => ?_
  have htest (j : ℕ) :
      gaussianCommonDivisorIdeal n ≤ I ^ (j + 1) ↔
        archivedIdealCharacter I = -1 ∧ (I.absNorm + 1) * p ^ j ∣ n := by
    simpa only [Nat.succ_sub_one] using
      gaussianCommonDivisor_le_prime_pow_iff hp hD ⟨I, hi⟩ hn (Nat.succ_pos j)
  simp_rw [htest]
  by_cases hsign : archivedIdealCharacter I = -1
  · let : I.IsPrime := ((mem_gaussianPrimesAbove p).mp hi).1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := ((mem_gaussianPrimesAbove p).mp hi).2
    have hnorm := (Ideal.pow_inertiaDeg p I).symm
    rw [hnorm, Nat.cast_pow, Real.log_pow]
    rcases (gaussianIndexPrime_shape hp).2 I hi with h | h <;> simp [hsign, h]
  · simp [hsign]

#print axioms archivedGaussianRawWindow_finite
#print axioms gaussianIndex_weighted_containment_at_prime

end
end AlpogeSuperZeta
