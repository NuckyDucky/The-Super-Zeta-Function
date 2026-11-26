import GaussianRawWindowRounding

/-! The half-window counts odd multiples below its upper endpoint.
Its discrete count can be replaced by length at every sparse address. -/

namespace AlpogeSuperZeta

open Finset
open scoped Classical

noncomputable section

/-- The count of multiples in `[x/2,x)` is the count of odd multiples below `x`. -/
theorem divisorWindowMultiplicity_eq_odd_prefix {x : ℝ} (hx : 0 ≤ x) {d : ℕ}
    (hd : 0 < d) :
    divisorWindowMultiplicity x d = ((⌈x / (d : ℝ)⌉₊ / 2 : ℕ) : ℝ) := by
  let a := ⌈x / (d : ℝ)⌉₊
  let b := ⌈x / (2 * (d : ℝ))⌉₊
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsplit : x / (d : ℝ) = 2 * (x / (2 * (d : ℝ))) := by ring
  have hab : a ≤ 2 * b := by
    apply Nat.ceil_le.mpr
    push_cast
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
  have hba : 2 * b < a + 2 := by
    have h : ((2 * b : ℕ) : ℝ) < ((a + 2 : ℕ) : ℝ) := by
      push_cast
      have hb := Nat.ceil_lt_add_one (div_nonneg hx (by positivity : (0 : ℝ) ≤ 2 * d))
      have ha := Nat.le_ceil (x / (d : ℝ))
      change (x / (d : ℝ)) ≤ (a : ℝ) at ha
      change (b : ℝ) < x / (2 * (d : ℝ)) + 1 at hb
      linarith
    exact_mod_cast h
  change (a : ℝ) - (b : ℝ) = ((a / 2 : ℕ) : ℝ)
  rw [← Nat.cast_sub (show b ≤ a by omega), show a - b = a / 2 by omega]

theorem mem_halfWindowOddPrefix {x : ℝ} {d k : ℕ} (hd : 0 < d) :
    k ∈ range (⌈x / (d : ℝ)⌉₊ / 2) ↔ ((d * (2 * k + 1) : ℕ) : ℝ) < x := by
  rw [mem_range, show k < ⌈x / (d : ℝ)⌉₊ / 2 ↔ 2 * k + 1 < ⌈x / (d : ℝ)⌉₊ by omega,
    Nat.lt_ceil, lt_div_iff₀ (Nat.cast_pos.mpr hd)]
  push_cast
  rw [mul_comm]

theorem divisorWindowMultiplicity_zero_of_le {x : ℝ} (hx : 0 ≤ x) {d : ℕ}
    (hd : 0 < d) (hxd : x ≤ d) : divisorWindowMultiplicity x d = 0 := by
  have h : ⌈x / (d : ℝ)⌉₊ ≤ 1 := Nat.ceil_le.mpr
    (by simpa using (div_le_one₀ (Nat.cast_pos.mpr hd)).mpr hxd)
  rw [divisorWindowMultiplicity_eq_odd_prefix hx hd, show ⌈x / (d : ℝ)⌉₊ / 2 = 0 by omega,
    Nat.cast_zero]

theorem divisorWindowMultiplicity_centered_error {x θ : ℝ} (hx : 0 < x)
    {d : ℕ} (hd : 0 < d) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |divisorWindowMultiplicity x d - x / (2 * (d : ℝ))| ≤ x ^ θ / (d : ℝ) ^ θ := by
  rw [← Real.div_rpow hx.le (Nat.cast_nonneg d)]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  by_cases hxd : x ≤ d
  · rw [divisorWindowMultiplicity_zero_of_le hx.le hd hxd, zero_sub, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ x / (2 * (d : ℝ)))]
    calc
      _ ≤ x / (d : ℝ) := by
        apply div_le_div_of_nonneg_left hx.le hd'
        linarith
      _ ≤ (x / (d : ℝ)) ^ θ := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (div_pos hx hd')
          ((div_le_one₀ hd').mpr hxd) hθ₁
  · exact (divisorWindowMultiplicity_rounding hd hx.le).le.trans
      (Real.one_le_rpow ((one_le_div₀ hd').mpr (le_of_not_ge hxd)) hθ₀)

/-- Sparse addresses have an explicit linear term and an error at the
same exponent as their summability threshold. -/
theorem divisorWindow_sparse_approximation {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hs : Summable (fun i => |b i| / (N i : ℝ) ^ θ)) {x : ℝ} (hx : 0 < x) :
    Summable (fun i => b i / (N i : ℝ)) ∧
      Summable (fun i => b i * divisorWindowMultiplicity x (N i)) ∧
      |(∑' i, b i * divisorWindowMultiplicity x (N i)) -
        (x / 2) * ∑' i, b i / (N i : ℝ)| ≤
        x ^ θ * ∑' i, |b i| / (N i : ℝ) ^ θ := by
  let l (i : ι) := b i / (N i : ℝ)
  let m (i : ι) := b i * divisorWindowMultiplicity x (N i)
  let e (i : ι) := m i - (x / 2) * l i
  have hl : Summable l := by
    apply Summable.of_abs
    refine hs.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_)
    have hNi : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
    have hpow : (N i : ℝ) ^ θ ≤ N i := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNi hθ₁
    have hAbsN : |(N i : ℝ)| = (N i : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [show l i = b i / (N i : ℝ) from rfl, abs_div, hAbsN]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hpow
  have hbound (i : ι) : |e i| ≤ x ^ θ * (|b i| / (N i : ℝ) ^ θ) := by
    have he : e i = b i * (divisorWindowMultiplicity x (N i) - x / (2 * (N i : ℝ))) := by
      dsimp [e, m, l]
      ring
    rw [he, abs_mul]
    calc
      _ ≤ |b i| * (x ^ θ / (N i : ℝ) ^ θ) :=
        mul_le_mul_of_nonneg_left (divisorWindowMultiplicity_centered_error hx (hN i) hθ₀ hθ₁)
          (abs_nonneg _)
      _ = _ := by ring
  have hE : Summable (fun i => |e i|) :=
    (hs.mul_left (x ^ θ)).of_nonneg_of_le (fun _ => abs_nonneg _) hbound
  have hm : Summable m := by
    simpa only [e, sub_add_cancel] using hE.of_abs.add (hl.mul_left (x / 2))
  refine ⟨hl, hm, ?_⟩
  change |(∑' i, m i) - (x / 2) * ∑' i, l i| ≤ _
  rw [← hl.tsum_mul_left, ← hm.tsum_sub (hl.mul_left (x / 2)), ← hs.tsum_mul_left]
  exact (by simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := e) (by simpa only [Real.norm_eq_abs] using hE) :
    |∑' i, e i| ≤ ∑' i, |e i|).trans (hE.tsum_le_tsum hbound (hs.mul_left (x ^ θ)))

#print axioms divisorWindowMultiplicity_eq_odd_prefix
#print axioms mem_halfWindowOddPrefix
#print axioms divisorWindow_sparse_approximation

end
end AlpogeSuperZeta
