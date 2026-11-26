import GaussianPrimeOnlyWindow

/-! Bounds for changing the indices in the prime ramp. Both the unit
shift and the addition of sparse terms have an exact linear correction. -/

namespace AlpogeSuperZeta

open Finset ArithmeticFunction

noncomputable section

/-- The ramp weight at an integer index. -/
def indexRampWeight (x : ℝ) (n : ℕ) : ℝ := max (x / (n : ℝ) - 1) 0

theorem indexRampWeight_eq (x : ℝ) (n : ℕ) :
    indexRampWeight x n = x / (n : ℝ) - min 1 (x / (n : ℝ)) := by
  unfold indexRampWeight
  by_cases h : x / (n : ℝ) ≤ 1
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), sub_self]
  · have h' := le_of_not_ge h
    rw [min_eq_left h', max_eq_left (sub_nonneg.mpr h')]

private theorem index_min_one_le_rpow {t θ : ℝ} (ht : 0 < t)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    min 1 t ≤ t ^ θ := by
  by_cases h : t ≤ 1
  · rw [min_eq_right h]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht h hθ₁
  · rw [min_eq_left (le_of_not_ge h), ← Real.one_rpow θ]
    exact Real.rpow_le_rpow zero_le_one (le_of_not_ge h) hθ₀

theorem indexRampWeight_zero_of_gt {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : x < (n : ℝ)) :
    indexRampWeight x n = 0 := by
  unfold indexRampWeight
  rw [max_eq_right (sub_nonpos.mpr ((div_le_one₀ (hx.trans_lt hn)).mpr hn.le))]

theorem summable_prime_log_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => Real.log p.val / (p.val : ℝ) ^ s) := by
  have h := (LSeriesSummable_vonMangoldt (s := (s : ℂ)) (by simpa using hs)).norm
  refine (h.comp_injective (show Function.Injective (fun p : Nat.Primes => p.val)
    from Subtype.coe_injective)).congr (fun p => ?_)
  have hlog : 0 ≤ Real.log (p.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  simp [LSeries.norm_term_eq, p.property.ne_zero, vonMangoldt_apply_prime p.property,
    Real.norm_eq_abs, abs_of_nonneg hlog]

/-- The pointwise loss after shifting an index by one and paying its
linear correction. -/
theorem index_shift_loss_bounds {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    0 ≤ min 1 (x / (n : ℝ)) - min 1 (x / ((n + 1 : ℕ) : ℝ)) ∧
      min 1 (x / (n : ℝ)) - min 1 (x / ((n + 1 : ℕ) : ℝ)) ≤
        min 1 (x / (n : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
  let t := x / (n : ℝ)
  let r := (n : ℝ) / ((n + 1 : ℕ) : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have ht : 0 ≤ t := div_nonneg hx hn'.le
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r ≤ 1 := (div_le_one₀ hs).mpr (by exact_mod_cast (Nat.le_succ n))
  have he : x / ((n + 1 : ℕ) : ℝ) = r * t := by dsimp [r, t]; field_simp
  rw [he]
  change 0 ≤ min 1 t - min 1 (r * t) ∧ min 1 t - min 1 (r * t) ≤ min 1 t / _
  have hlow : r * min 1 t ≤ min 1 (r * t) := le_min
    ((mul_le_of_le_one_right hr (min_le_left _ _)).trans hr₁)
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hr)
  have hu : min 1 (r * t) ≤ min 1 t :=
    min_le_min le_rfl (mul_le_of_le_one_left ht hr₁)
  have hdiff : 1 - r = 1 / ((n + 1 : ℕ) : ℝ) := by
    dsimp [r]
    push_cast
    field_simp
    ring
  refine ⟨sub_nonneg.mpr hu, ?_⟩
  rw [div_eq_mul_one_div, ← hdiff]
  linarith only [hlow]

/-- A summable family of weighted indices contributes a linear term,
with a nonnegative loss bounded by its exponent-weighted sum. -/
theorem centered_index_ramp_bounds {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hb : ∀ i, 0 ≤ b i) (hN : ∀ i, 0 < N i) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hs : Summable (fun i => b i / (N i : ℝ) ^ θ)) {x : ℝ} (hx : 0 < x) :
    0 ≤ x * (∑' i, b i / (N i : ℝ)) - (∑' i, b i * indexRampWeight x (N i)) ∧
      x * (∑' i, b i / (N i : ℝ)) - (∑' i, b i * indexRampWeight x (N i)) ≤
        x ^ θ * (∑' i, b i / (N i : ℝ) ^ θ) := by
  have hp (i) : 0 < (N i : ℝ) := by exact_mod_cast hN i
  have hge (i) : 1 ≤ (N i : ℝ) := by exact_mod_cast hN i
  have hlin : Summable (fun i => b i / (N i : ℝ)) :=
    hs.of_nonneg_of_le (fun i => div_nonneg (hb i) (hp i).le) (fun i => by
      apply div_le_div_of_nonneg_left (hb i) (Real.rpow_pos_of_pos (hp i) _)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hge i) hθ₁)
  have hlinx := hlin.mul_left x
  have hramp : Summable (fun i => b i * indexRampWeight x (N i)) :=
    hlinx.of_nonneg_of_le (fun i => mul_nonneg (hb i) (le_max_right _ _)) (fun i => by
      rw [indexRampWeight, show x * (b i / (N i : ℝ)) = b i * (x / (N i : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left
        (max_le (sub_le_self _ zero_le_one) (div_nonneg hx.le (hp i).le)) (hb i))
  have heq (i) :
      x * (b i / (N i : ℝ)) - b i * indexRampWeight x (N i) =
        b i * min 1 (x / (N i : ℝ)) := by rw [indexRampWeight_eq]; ring
  have herr := (hlinx.sub hramp).congr heq
  rw [← hlin.tsum_mul_left, ← hlinx.tsum_sub hramp, tsum_congr heq]
  refine ⟨tsum_nonneg (fun i => mul_nonneg (hb i) (le_min zero_le_one (by positivity))), ?_⟩
  rw [← hs.tsum_mul_left]
  apply herr.tsum_le_tsum _ (hs.mul_left _)
  intro i
  calc
    _ ≤ b i * (x / (N i : ℝ)) ^ θ :=
      mul_le_mul_of_nonneg_left (index_min_one_le_rpow (div_pos hx (hp i)) hθ₀ hθ₁) (hb i)
    _ = _ := by rw [Real.div_rpow hx.le (hp i).le]; ring

/-- Shift all positive indices by one. The linear correction and its
bounded loss are computed from the same weights. -/
theorem centered_index_shift_bounds (b : ℕ → ℝ) (hb₀ : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hs : Summable (fun n : ℕ => b n / (n : ℝ) ^ (1 + θ))) {x : ℝ} (hx : 0 < x) :
    let loss :=
      x * (∑' n : ℕ, b n / (n : ℝ) / ((n + 1 : ℕ) : ℝ)) -
        ∑ n ∈ range (⌊x⌋₊ + 1), b n * (indexRampWeight x n - indexRampWeight x (n + 1))
    0 ≤ loss ∧ loss ≤ x ^ θ * (∑' n : ℕ, b n / (n : ℝ) ^ (1 + θ)) := by
  let f (n : ℕ) := b n / (n : ℝ) / ((n + 1 : ℕ) : ℝ)
  let e (n : ℕ) := b n * (indexRampWeight x n - indexRampWeight x (n + 1))
  let l (n : ℕ) := b n * (min 1 (x / (n : ℝ)) - min 1 (x / ((n + 1 : ℕ) : ℝ)))
  let S := range (⌊x⌋₊ + 1)
  have hf : Summable f := hs.of_nonneg_of_le
    (fun n => div_nonneg (div_nonneg (hb n) (Nat.cast_nonneg n)) (Nat.cast_nonneg _)) (fun n => by
    rcases n with _ | n
    · simp [f, hb₀]
    · have h : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have h1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have he : (((n + 1 : ℕ) : ℝ) ^ θ) ≤ (n + 1 : ℕ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 hθ₁
      dsimp only [f]
      rw [div_div, Real.rpow_add h, Real.rpow_one]
      exact div_le_div_of_nonneg_left (hb _) (by positivity)
        (mul_le_mul_of_nonneg_left
          (he.trans (by exact_mod_cast Nat.le_succ (n + 1))) h.le))
  have he0 (n : ℕ) (hn : n ∉ S) : e n = 0 := by
    have h : x < (n : ℝ) := Nat.lt_of_floor_lt (by simpa [S] using hn)
    have h' : x < ((n + 1 : ℕ) : ℝ) :=
      h.trans_le (by exact_mod_cast Nat.le_succ n)
    simp [e, indexRampWeight_zero_of_gt hx.le h, indexRampWeight_zero_of_gt hx.le h']
  have he : HasSum e (∑ n ∈ S, e n) := hasSum_sum_of_ne_finset_zero he0
  have hterm (n : ℕ) : x * f n - e n = l n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f, e, l, hb₀]
    · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hp' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      simp only [f, e, l, indexRampWeight_eq]
      push_cast
      field_simp
      ring
  have hl := (hf.hasSum.mul_left x).sub he
  rw [show (fun n => x * f n - e n) = l from funext hterm] at hl
  have hlow (n : ℕ) : 0 ≤ l n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [l, hb₀]
    · exact mul_nonneg (hb n) (index_shift_loss_bounds hx.le hn.bot_lt).1
  change 0 ≤ x * (∑' n, f n) - ∑ n ∈ S, e n ∧
    x * (∑' n, f n) - ∑ n ∈ S, e n ≤ x ^ θ * (∑' n : ℕ, b n / (n : ℝ) ^ (1 + θ))
  rw [← hl.tsum_eq, ← hs.tsum_mul_left]
  refine ⟨tsum_nonneg hlow, hl.summable.tsum_le_tsum ?_ (hs.mul_left _)⟩
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [l, hb₀]
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr hn.bot_lt
  calc
    l n ≤ b n * (min 1 (x / (n : ℝ)) / ((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (index_shift_loss_bounds hx.le hn.bot_lt).2 (hb n)
    _ ≤ b n * ((x / (n : ℝ)) ^ θ / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (hb n)
      exact div_le_div_of_nonneg_left (le_min zero_le_one (by positivity)) hp
        (by exact_mod_cast Nat.le_succ n) |>.trans
          (div_le_div_of_nonneg_right (index_min_one_le_rpow (div_pos hx hp) hθ₀ hθ₁) hp.le)
    _ = _ := by rw [Real.div_rpow hx.le hp.le, Real.rpow_add hp, Real.rpow_one]; ring

#print axioms centered_index_ramp_bounds
#print axioms centered_index_shift_bounds

end
end AlpogeSuperZeta
