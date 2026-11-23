import QuarticPrefix
import QuarticThetaTail

namespace QuarticKernel

noncomputable def headBins (n : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (prefixSum (i+1) : ℝ)*r^(i+1)

noncomputable def remainderBound (N : ℕ) (r : ℝ) : ℝ :=
  2*r^(N+1)*((N:ℝ)+1+r/(1-r))

theorem theta_head_and_tail (n : ℕ) {u : ℝ} (hu : 0 < u) :
    let r := Real.exp (-u)
    theta u = (1-r)*headBins n r + (prefixSum (n+1) : ℝ)*r^(n+1) +
      ∑' i : ℕ, (coeff (n+2+i) : ℝ)*r^(n+2+i) := by
  let r := Real.exp (-u)
  let f (j : ℕ) := (coeff j : ℝ)*r^j
  have h : Summable f := theta_summable hu
  have hfirst := h.sum_add_tsum_nat_add 1
  have hshift : Summable (fun j => f (j+1)) :=
    h.comp_injective fun _ _ he => Nat.add_right_cancel he
  have hcut := hshift.sum_add_tsum_nat_add (n+1)
  have hshift_eq (i : ℕ) : f (i+(n+1)+1) = f (n+2+i) := by
    congr 1
    omega
  change _ = (1-r)*headBins n r + (prefixSum (n+1):ℝ)*r^(n+1) + ∑' i, f (n+2+i)
  change _ + (∑' j, f (j+1)) = theta u at hfirst
  simp only [Finset.sum_range_one, f, coeff_zero, Int.cast_zero, zero_mul,
    zero_add] at hfirst
  rw [← hfirst, ← hcut]
  simp only [hshift_eq]
  congr 1
  change (∑ j ∈ Finset.range (n+1), (coeff (j+1) : ℝ)*r^(j+1)) = _
  rw [prefix_abel, Finset.sum_range_succ, headBins, pow_succ r (n+1)]
  ring

private theorem remainder_monotone (N : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hR : R < 1)
    (h : r ≤ R) : remainderBound N r ≤ remainderBound N R := by
  have hfrac : r/(1-r) ≤ R/(1-R) := by
    apply (div_le_div_iff₀ (sub_pos.mpr (h.trans_lt hR)) (sub_pos.mpr hR)).2
    linarith
  unfold remainderBound
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr h _) (by norm_num)
  · linarith
  · have hdiv := div_nonneg hr (sub_pos.mpr (h.trans_lt hR)).le
    linarith [show (0:ℝ) ≤ (N:ℝ) by positivity]
  · exact mul_nonneg (by norm_num) (pow_nonneg (hr.trans h) _)

/-- Monotone endpoint bounds for the finite Abel sum and the omitted
coefficients. The numerical inputs are bounds for the actual prefix bins. -/
theorem theta_cell_bounds (n : ℕ) {u rlo rhi lo hi : ℝ} (hu : 0 < u)
    (hrlo : 0 ≤ rlo) (hrhi : rhi < 1)
    (hleft : rlo ≤ Real.exp (-u)) (hright : Real.exp (-u) ≤ rhi)
    (hp : ∀ j : ℕ, j < n → 0 ≤ prefixSum (j+1))
    (hN : 0 ≤ prefixSum (n+1))
    (hl : 0 ≤ lo) (hlo : lo ≤ headBins n rlo) (hhi : headBins n rhi ≤ hi) :
    (1-rhi)*lo + (prefixSum (n+1):ℝ)*rlo^(n+1) - remainderBound (n+1) rhi ≤ theta u ∧
      theta u ≤ (1-rlo)*hi + (prefixSum (n+1):ℝ)*rhi^(n+1) +
        remainderBound (n+1) rhi := by
  let r := Real.exp (-u)
  have hr := Real.exp_pos (-u)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hmono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : headBins n s ≤ headBins n t := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst _)
      (by exact_mod_cast hp j (Finset.mem_range.mp hj))
  have h₁ := hlo.trans (hmono hrlo hleft)
  have h₂ := (hmono hr.le hright).trans hhi
  have h₃ : (1-rhi)*lo ≤ (1-r)*headBins n r :=
    mul_le_mul (by linarith) h₁ hl (sub_nonneg.mpr hr1.le)
  have h₄ : (1-r)*headBins n r ≤ (1-rlo)*hi :=
    mul_le_mul (by linarith) h₂ (hl.trans h₁) (by linarith)
  have hNl := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrlo hleft (n+1))
    (show 0 ≤ (prefixSum (n+1):ℝ) by exact_mod_cast hN)
  have hNu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hright (n+1))
    (show 0 ≤ (prefixSum (n+1):ℝ) by exact_mod_cast hN)
  have ht := abs_le.mp ((theta_tail_abs (n+1) hr hr1).trans
    (remainder_monotone (n+1) hr.le hrhi hright))
  have he := theta_head_and_tail n hu
  change theta u = (1-r)*headBins n r + (prefixSum (n+1):ℝ)*r^(n+1) + _ at he
  rw [he]
  constructor <;> linarith [ht.1, ht.2]

#print axioms theta_head_and_tail
#print axioms theta_cell_bounds

end QuarticKernel
