import QuarticArithmetic

open scoped BigOperators

namespace QuarticKernel

noncomputable def prefixSum (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, coeff (i+1)

private theorem prefixSum_succ (n : ℕ) : prefixSum (n+1) = prefixSum n + coeff (n+1) :=
  Finset.sum_range_succ _ _

def scanPositive (n : ℕ) (accumulated : ℤ) : ℕ → Bool
  | 0 => true
  | k+1 =>
    let next := accumulated + evalCoeff (n+1)
    decide (1 ≤ next) && scanPositive (n+1) next k

private theorem scanPositive_sound (n k : ℕ)
    (h : scanPositive n (prefixSum n) k = true) :
    ∀ j : ℕ, n < j → j ≤ n+k → 1 ≤ prefixSum j := by
  induction k generalizing n with
  | zero => intro j h₁ h₂; omega
  | succ k ih =>
    simp only [scanPositive, evalCoeff_eq, ← prefixSum_succ, Bool.and_eq_true,
      decide_eq_true_eq] at h
    intro j h₁ h₂
    by_cases hj : j = n+1
    · simpa only [hj] using h.1
    · exact ih (n+1) h.2 j (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem checked_prefix : ∀ n : ℕ, 0 < n → n ≤ 128 → 1 ≤ prefixSum n := by
  have h : scanPositive 0 0 128 = true := by decide
  apply scanPositive_sound 0 128
  simpa [prefixSum] using h

theorem prefix_abel (r : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (coeff (i+1) : ℝ)*r^(i+1)) =
      (1-r) * (∑ i ∈ Finset.range n, (prefixSum (i+1) : ℝ)*r^(i+1)) +
        (prefixSum n : ℝ) * r^(n+1) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih, prefixSum_succ, Int.cast_add, pow_succ r (n+1)]
    ring

private theorem telescoping (r : ℝ) (n : ℕ) :
    (1-r) * (∑ i ∈ Finset.range n, r^(i+1)) + r^(n+1) = r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ r (n+1)]
    linarith [show (1-r) * r^(n+1) + r^(n+1)*r = r^(n+1) by ring]

private theorem finite_head {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    r ≤ ∑ i ∈ Finset.range 128, (coeff (i+1) : ℝ)*r^(i+1) := by
  rw [prefix_abel]
  conv_lhs => rw [← telescoping r 128]
  have ht (i : ℕ) (hi : i ∈ Finset.range 128) : (1 : ℝ) ≤ ↑(prefixSum (i+1)) := by
    have h := Finset.mem_range.mp hi
    exact_mod_cast checked_prefix (i+1) (by omega) (by omega)
  have hn : (1:ℝ) ≤ (prefixSum 128 : ℝ) := by
    exact_mod_cast checked_prefix 128 (by decide) (by decide)
  have h₁ : (∑ i ∈ Finset.range 128, r^(i+1)) ≤
      ∑ i ∈ Finset.range 128, (prefixSum (i+1) : ℝ)*r^(i+1) := by
    refine Finset.sum_le_sum fun i hi => ?_
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ht i hi) (pow_nonneg hr _)
  exact add_le_add (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hr₁))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (pow_nonneg hr 129))

private theorem finite_tail {r : ℝ} (hr : 0 < r) (hrq : r ≤ 11/12) :
    |∑' i : ℕ, (coeff (i+129) : ℝ)*r^(i+129)| < r/2 := by
  let q : ℝ := 11/12
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hq₀ : 0 ≤ q := by norm_num [q]
  have hg := ((hasSum_geometric_of_norm_lt_one hq).mul_left (129:ℝ)).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hq)
  have hg' : HasSum (fun i : ℕ => r * q^128 * ((i:ℝ)+129) * q^i)
      (r * q^128 * (129/(1-q) + q/(1-q)^2)) := by
    convert hg.mul_left (r * q^128) using 1
    ext i
    ring
  have ht (i : ℕ) : ‖(coeff (i+129) : ℝ)*r^(i+129)‖ ≤ r * q^128 * ((i:ℝ)+129) * q^i := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
    have hp : r^(i+129) ≤ r * q^128 * q^i := by
      rw [show i+129 = (128+i)+1 by omega, pow_succ', pow_add r 128 i]
      calc
        _ ≤ r * (q^128 * q^i) := by
          refine mul_le_mul_of_nonneg_left ?_ hr.le
          exact mul_le_mul (pow_le_pow_left₀ hr.le hrq 128) (pow_le_pow_left₀ hr.le hrq i)
            (pow_nonneg hr.le _) (pow_nonneg hq₀ _)
        _ = _ := by ring
    have hcoeff : |(coeff (i+129) : ℝ)| ≤ (i:ℝ)+129 := by
      simpa using coeff_abs_le (i+129)
    exact (mul_le_mul hcoeff hp (pow_nonneg hr.le _) (by positivity)).trans_eq (by ring)
  have h := tsum_of_norm_bounded hg' ht
  rw [Real.norm_eq_abs] at h
  apply h.trans_lt
  have hb : q^128 * (129/(1-q) + q/(1-q)^2) < 1/2 := by norm_num [q]
  calc
    _ = r * (q^128 * (129/(1-q) + q/(1-q)^2)) := by ring
    _ < r*(1/2) := mul_lt_mul_of_pos_left hb hr
    _ = _ := by ring

theorem theta_pos_of_one_eleventh_le {u : ℝ} (hu : 1/11 ≤ u) : 0 < theta u := by
  have hu₀ : 0 < u := by linarith
  let r := Real.exp (-u)
  have hr : 0 < r := Real.exp_pos _
  have hrq : r ≤ 11/12 := by
    have he : (12/11 : ℝ) ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    dsimp [r]
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using he
  let f : ℕ → ℝ := fun i => (coeff i : ℝ)*r^i
  have hs : Summable f := theta_summable hu₀
  have hshift : Summable (fun i => f (i+1)) :=
    hs.comp_injective (fun a b hab => Nat.add_right_cancel hab)
  have hzero := hs.sum_add_tsum_nat_add 1
  have hsplit := hshift.sum_add_tsum_nat_add 128
  have htheta : theta u = (∑ i ∈ Finset.range 128, (coeff (i+1) : ℝ)*r^(i+1)) +
      ∑' i : ℕ, (coeff (i+129) : ℝ)*r^(i+129) := by
    change (∑ i ∈ Finset.range 1, f i) + (∑' i, f (i+1)) = theta u at hzero
    simp only [Finset.sum_range_one, f, coeff_zero, Int.cast_zero, zero_mul, zero_add] at hzero
    rw [← hzero, ← hsplit]
  have hhead := finite_head hr.le (hrq.trans (by norm_num))
  have htail := abs_lt.mp (finite_tail hr hrq)
  linarith

theorem kernel_pos_after_12 {x : ℝ} (hx : 12 ≤ x) : 0 < kernel x := by
  apply mul_pos (Real.exp_pos _)
  apply theta_pos_of_one_eleventh_le
  apply (le_div_iff₀ scale_pos).mpr
  have hE : (150000 : ℝ) < Real.exp 12 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.71828)
      (show (2.71828 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 12
    rw [show Real.exp 1^12 = Real.exp (12:ℝ) by norm_num [← Real.exp_nat_mul]] at h
    norm_num at h ⊢
    linarith
  have hxE := Real.exp_le_exp.mpr hx
  linarith [scale_lt]

theorem theta_pos_of_quarter_le {u : ℝ} (hu : 1/4 ≤ u) : 0 < theta u :=
  theta_pos_of_one_eleventh_le (le_trans (by norm_num) hu)

theorem kernel_pos_after_13 {x : ℝ} (hx : 13 ≤ x) : 0 < kernel x :=
  kernel_pos_after_12 ((by norm_num : (12:ℝ) ≤ 13).trans hx)

#print axioms checked_prefix
#print axioms kernel_pos_after_12
#print axioms kernel_pos_after_13

end QuarticKernel


