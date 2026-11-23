import QuarticCellBounds

namespace QuarticKernel

private theorem telescope_head (r : ℝ) (n : ℕ) :
    (1-r) * (∑ i ∈ Finset.range n, r^(i+1)) + r^(n+1) = r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ r (n+1)]
    linarith [show (1-r)*r^(n+1) + r^(n+1)*r = r^(n+1) by ring]

/-- The constant-one prefix sequence is a lower envelope for the finite
Abel sum. Its geometric sum collapses to a single exponential. -/
theorem theta_ge_exp_sub_remainder (n : ℕ) {u : ℝ} (hu : 0 < u)
    (hp : ∀ j : ℕ, 0 < j → j ≤ n+1 → 1 ≤ prefixSum j) :
    let r := Real.exp (-u)
    r - remainderBound (n+1) r ≤ theta u := by
  let r := Real.exp (-u)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hb : (∑ i ∈ Finset.range n, r^(i+1)) ≤ headBins n r := by
    apply Finset.sum_le_sum
    intro i hi
    have hii := Finset.mem_range.mp hi
    have ha : (1 : ℝ) ≤ ↑(prefixSum (i+1)) := by
      exact_mod_cast hp (i+1) (by omega) (by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (pow_nonneg hr.le (i+1))
  have hN : (1 : ℝ) ≤ ↑(prefixSum (n+1)) := by exact_mod_cast hp (n+1) (by omega) le_rfl
  have hf := add_le_add (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hr1.le))
    (mul_le_mul_of_nonneg_right hN (pow_nonneg hr.le (n+1)))
  rw [one_mul, telescope_head] at hf
  have ht := (abs_le.mp (theta_tail_abs (n+1) hr hr1)).1
  have he := theta_head_and_tail n hu
  change theta u = (1-r)*headBins n r + (prefixSum (n+1):ℝ)*r^(n+1) + _ at he
  change r - 2*r^((n+1)+1)*((↑(n+1):ℝ)+1+r/(1-r)) ≤ theta u
  linarith only [hf, ht, he]

private theorem exp_quotient_le_inv {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) / (1 - Real.exp (-u)) ≤ 1/u := by
  rw [Real.exp_neg]
  have hE := Real.exp_pos u
  have hE1 := Real.one_lt_exp_iff.mpr hu
  have hden : 0 < 1 - (Real.exp u)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hE1)
  apply (div_le_div_iff₀ hden hu).mpr
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ hE).mpr
  have he := Real.add_one_le_exp u
  calc
    u ≤ Real.exp u - 1 := by linarith
    _ = 1 * (1-(Real.exp u)⁻¹) * Real.exp u := by
      field_simp [hE.ne']

/-- At the center the omitted shell tail is less than the first term.
The same closed-form inequality holds throughout the right half-line. -/
theorem actual_remainder_lt_first {u : ℝ} (hu : 1/scale ≤ u) :
    remainderBound 33554432 (Real.exp (-u)) < Real.exp (-u) := by
  let r := Real.exp (-u)
  have hu₀ : 0 < u := (one_div_pos.mpr scale_pos).trans_le hu
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu₀)
  have hNu : (20:ℝ) ≤ 33554432*u := by
    have h := (div_le_iff₀ scale_pos).mp hu
    nlinarith only [h, scale_lt, hu₀]
  have hU : 1/u ≤ scale := by
    apply (div_le_iff₀ hu₀).mpr
    convert (div_le_iff₀ scale_pos).mp hu using 1
    ring
  have hq : r/(1-r) ≤ 1640000 := (exp_quotient_le_inv hu₀).trans
    (hU.trans scale_lt.le)
  have he20 : (400000000:ℝ) < Real.exp 20 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
      (show (2.7:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 20
    rw [show Real.exp 1^20 = Real.exp (20:ℝ) by norm_num [← Real.exp_nat_mul]] at h
    exact (by norm_num : (400000000:ℝ) < (2.7:ℝ)^20).trans_le h
  have hrN : r^33554432 ≤ 1/400000000 := by
    dsimp only [r]
    rw [← Real.exp_nat_mul]
    change Real.exp ((33554432:ℝ) * -u) ≤ 1/400000000
    have hex : (400000000:ℝ) ≤ Real.exp (33554432*u) :=
      he20.le.trans (Real.exp_le_exp.mpr hNu)
    rw [show (33554432:ℝ) * -u = -(33554432*u) by ring, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hex
  change 2*r^(33554432+1)*((↑(33554432:ℕ):ℝ)+1+r/(1-r)) < r
  rw [pow_succ]
  push_cast
  have hcoef : 2 * r^(33554432:ℕ) * (33554432+1+r/(1-r)) < 1 := by
    calc
      2 * r^(33554432:ℕ) * (33554432+1+r/(1-r)) ≤
          2*(1/400000000)*(33554432+1+1640000) :=
        mul_le_mul (by linarith only [hrN]) (by linarith only [hq])
          (by
            have hf : 0 ≤ r/(1-r) := div_nonneg hr.le (sub_pos.mpr hr1).le
            linarith only [hf]) (by norm_num)
      _ < 1 := by norm_num
  calc
    _ = (2*r^(33554432:ℕ)*(33554432+1+r/(1-r)))*r := by ring
    _ < 1*r := mul_lt_mul_of_pos_right hcoef hr
    _ = r := one_mul r

theorem kernel_pos_of_actual_prefix
    (hp : ∀ j : ℕ, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j)
    {x : ℝ} (hx : 0 ≤ x) : 0 < kernel x := by
  have hu : 1/scale ≤ Real.exp x/scale :=
    div_le_div_of_nonneg_right (Real.one_le_exp_iff.mpr hx) scale_pos.le
  have hu₀ := (one_div_pos.mpr scale_pos).trans_le hu
  have hb := theta_ge_exp_sub_remainder 33554431 hu₀ hp
  have ht := actual_remainder_lt_first hu
  change 0 < Real.exp (x/2)*theta (Real.exp x/scale)
  exact mul_pos (Real.exp_pos _) ((sub_pos.mpr ht).trans_le hb)

#print axioms theta_ge_exp_sub_remainder
#print axioms actual_remainder_lt_first
#print axioms kernel_pos_of_actual_prefix

end QuarticKernel
