import GaussianHalfWindowMultiplicity

/-! Moving an address from `p` to `p+1` loses an odd multiple only
at an endpoint where `m*p < x ≤ m*(p+1)`. For large `p`, this
provides a finite bound without a summation over the large primes. -/

namespace AlpogeSuperZeta

open Finset
open scoped Classical

noncomputable section

theorem divisorWindow_shift_large {x : ℝ} (hx : 1 ≤ x) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Real.sqrt x < (p : ℝ)) (b : ℕ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : ∀ p ∈ P, 0 ≤ b p ∧ b p ≤ W) :
    0 ≤ ∑ p ∈ P, b p * (divisorWindowMultiplicity x p - divisorWindowMultiplicity x (p + 1)) ∧
    (∑ p ∈ P, b p * (divisorWindowMultiplicity x p - divisorWindowMultiplicity x (p + 1))) ≤
      W * Real.sqrt x := by
  let J (p : ℕ) := ⌈x / (p : ℝ)⌉₊ / 2
  let T (p : ℕ) := Ico (J (p + 1)) (J p)
  let S := P.sigma T
  have hx₀ := zero_le_one.trans hx
  have hp₀ {p : ℕ} (hp : p ∈ P) : 0 < p :=
    Nat.cast_pos.mp ((Real.sqrt_nonneg x).trans_lt (hP p hp))
  have hJ {p : ℕ} (hp : 0 < p) : J (p + 1) ≤ J p := by
    apply Nat.div_le_div_right
    apply Nat.ceil_le_ceil
    apply div_le_div_of_nonneg_left hx₀ (Nat.cast_pos.mpr hp)
    exact_mod_cast Nat.le_succ p
  have hT {p : ℕ} (hp : 0 < p) :
      ((T p).card : ℝ) = divisorWindowMultiplicity x p - divisorWindowMultiplicity x (p + 1) := by
    rw [divisorWindowMultiplicity_eq_odd_prefix hx₀ hp,
      divisorWindowMultiplicity_eq_odd_prefix hx₀ (Nat.succ_pos p)]
    change ((Ico (J (p + 1)) (J p)).card : ℝ) = (J p : ℝ) - (J (p + 1) : ℝ)
    rw [Nat.card_Ico, Nat.cast_sub (hJ hp)]
  have hregion {p k : ℕ} (hp : 0 < p) (hk : k ∈ T p) :
      ((p * (2 * k + 1) : ℕ) : ℝ) < x ∧ x ≤ (((p + 1) * (2 * k + 1) : ℕ) : ℝ) := by
    obtain ⟨hl, hu⟩ := mem_Ico.mp hk
    refine ⟨(mem_halfWindowOddPrefix hp).mp (mem_range.mpr hu), le_of_not_gt fun h => ?_⟩
    exact (not_lt_of_ge hl) (mem_range.mp ((mem_halfWindowOddPrefix (Nat.succ_pos p)).mpr h))
  have hcount :
      S.card ≤ (range (⌈Real.sqrt x⌉₊ / 2)).card := by
    apply card_le_card_of_injOn (fun pk : Sigma fun _ : ℕ => ℕ => pk.2)
    · rintro ⟨p, k⟩ hk
      obtain ⟨hp, ht⟩ := mem_sigma.mp hk
      have hh := (hregion (hp₀ hp) ht).1
      have hk' : ((2 * k + 1 : ℕ) : ℝ) < Real.sqrt x := by
        by_contra! h
        have he : x ≤ ((p * (2 * k + 1) : ℕ) : ℝ) := by
          calc
            x = Real.sqrt x * Real.sqrt x := by nlinarith [Real.sq_sqrt hx₀]
            _ ≤ (p : ℝ) * ((2 * k + 1 : ℕ) : ℝ) :=
              mul_le_mul (hP p hp).le h (Real.sqrt_nonneg x) (Nat.cast_nonneg p)
            _ = _ := (Nat.cast_mul _ _).symm
        exact (not_lt_of_ge he) hh
      change k ∈ range (⌈Real.sqrt x⌉₊ / 2)
      simpa only [Nat.cast_one, div_one] using
        (mem_halfWindowOddPrefix (d := 1) (x := Real.sqrt x) (k := k) (by decide)).mpr
          (by simpa only [one_mul] using hk')
    · rintro ⟨p, k⟩ hp ⟨q, l⟩ hq h
      change k = l at h
      subst l
      obtain ⟨hpP, hpT⟩ := mem_sigma.mp hp
      obtain ⟨hqP, hqT⟩ := mem_sigma.mp hq
      have hp' := hregion (hp₀ hpP) hpT
      have hq' := hregion (hp₀ hqP) hqT
      have hcompare {r s : ℕ} (h : r < s) :
          (((r + 1) * (2 * k + 1) : ℕ) : ℝ) ≤ ((s * (2 * k + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_right (2 * k + 1) (Nat.succ_le_of_lt h)
      have hl : ¬p < q := fun h => (not_lt_of_ge (hp'.2.trans (hcompare h))) hq'.1
      have hu : ¬q < p := fun h => (not_lt_of_ge (hq'.2.trans (hcompare h))) hp'.1
      exact congrArg (fun n => Sigma.mk n k) (by omega : p = q)
  have hcard : (S.card : ℝ) ≤ Real.sqrt x := by
    rw [card_range] at hcount
    have ha : (S.card : ℝ) ≤ ((⌈Real.sqrt x⌉₊ / 2 : ℕ) : ℝ) := by exact_mod_cast hcount
    have hb : ((⌈Real.sqrt x⌉₊ / 2 : ℕ) : ℝ) * 2 ≤ (⌈Real.sqrt x⌉₊ : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self ⌈Real.sqrt x⌉₊ 2
    linarith [Nat.ceil_lt_add_one (Real.sqrt_nonneg x), Real.one_le_sqrt.mpr hx]
  constructor
  · apply sum_nonneg
    intro p hp
    rw [← hT (hp₀ hp)]
    exact mul_nonneg (hb p hp).1 (Nat.cast_nonneg _)
  · calc
      _ = ∑ p ∈ P, b p * ((T p).card : ℝ) :=
        sum_congr rfl fun p hp => by rw [hT (hp₀ hp)]
      _ ≤ ∑ p ∈ P, W * ((T p).card : ℝ) :=
        sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hb p hp).2 (Nat.cast_nonneg _)
      _ = W * (S.card : ℝ) := by rw [← mul_sum]; simp only [S, card_sigma, Nat.cast_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard hW

#print axioms divisorWindow_shift_large

end
end AlpogeSuperZeta
