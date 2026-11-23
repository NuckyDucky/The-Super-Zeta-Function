import QuarticShellCount

namespace QuarticKernel

private theorem abel_tsum {r : ℝ} {a b : ℕ → ℝ}
    (ha : Summable (fun i => a i * r^i)) (hb : Summable (fun i => b i * r^i))
    (h₀ : b 0 = a 0) (hs : ∀ i, b (i+1) = b i + a (i+1)) :
    (∑' i, a i*r^i) = (1-r) * ∑' i, b i*r^i := by
  let A (i : ℕ) := a i*r^i
  let B (i : ℕ) := b i*r^i
  have hb' : Summable (fun i => B (i+1)) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hA := ha.sum_add_tsum_nat_add 1
  have hB := hb.sum_add_tsum_nat_add 1
  change (∑ i ∈ Finset.range 1, A i) + (∑' i, A (i+1)) = (∑' i, A i) at hA
  change (∑ i ∈ Finset.range 1, B i) + (∑' i, B (i+1)) = (∑' i, B i) at hB
  have hh (i : ℕ) : A (i+1) = B (i+1) - r*B i := by
    dsimp [A, B]
    rw [hs i, pow_succ]
    ring
  have he : (∑' i, A (i+1)) = (∑' i, B (i+1)) - r*(∑' i, B i) := by
    simp_rw [hh]
    rw [hb'.tsum_sub (hb.mul_left r), tsum_mul_left]
  change (∑' i, A i) = (1-r)*(∑' i, B i)
  have hAB : A 0 = B 0 := by simp [A, B, h₀]
  simp only [Finset.sum_range_one] at hA hB
  rw [sub_mul, one_mul]
  linarith only [hA, hB, hAB, he]

private theorem abs_tail_prefix (N i : ℕ) :
    (∑ j ∈ Finset.range (i+1), |(coeff (N+1+j) : ℝ)|) ≤ 2*((N:ℝ)+1+i) := by
  have h := coefficient_count_bound (N+1+i)
  rw [show N+1+i+1 = (N+1)+(i+1) by omega, Finset.sum_range_add] at h
  have h₀ : (0:ℤ) ≤ ∑ j ∈ Finset.range (N+1), |coeff j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (coeff j)
  have hb : (∑ j ∈ Finset.range (i+1), |coeff (N+1+j)|) ≤ 2*(N+1+i : ℕ) := by
    push_cast at h ⊢
    linarith only [h, h₀]
  exact_mod_cast hb

/-- The sharper lattice-count tail applies at every grid node, including
the smallest exponent at the center. -/
theorem theta_tail_abs (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    |∑' i : ℕ, (coeff (N+1+i) : ℝ)*r^(N+1+i)| ≤
      2*r^(N+1)*((N:ℝ)+1+r/(1-r)) := by
  let a (i : ℕ) := |(coeff (N+1+i):ℝ)|
  let b (i : ℕ) := ∑ j ∈ Finset.range (i+1), a j
  let g (i : ℕ) := (2*((N:ℝ)+1+i))*r^i
  have hR : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hG : HasSum g (2*((N+1 : ℝ)/(1-r)+r/(1-r)^2)) := by
    convert ((((hasSum_geometric_of_norm_lt_one hR).mul_left ((N:ℝ)+1)).add
      (hasSum_coe_mul_geometric_of_norm_lt_one hR)).mul_left (2:ℝ)) using 1
    ext i
    dsimp [g]
    ring
  have hb0 (i : ℕ) : 0 ≤ b i := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hb1 (i : ℕ) : b i*r^i ≤ g i := mul_le_mul_of_nonneg_right (abs_tail_prefix N i)
    (pow_nonneg hr.le _)
  have hb : Summable (fun i => b i*r^i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hb0 i) (pow_nonneg hr.le _)) hb1 hG.summable
  have hab (i : ℕ) : a i ≤ b i := by
    dsimp only [b]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => abs_nonneg _)
  have ha : Summable (fun i => a i*r^i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))
      (fun i => mul_le_mul_of_nonneg_right (hab i) (pow_nonneg hr.le _)) hb
  have hAbs := abel_tsum ha hb (by simp [b]) (fun i => Finset.sum_range_succ a (i+1))
  have h := mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hb1 hb hG.summable)
    (sub_nonneg.mpr hr1.le)
  have h2 : (∑' i, a i*r^i) ≤ 2*((N:ℝ)+1+r/(1-r)) := by
    rw [hAbs, hG.tsum_eq] at *
    refine h.trans_eq ?_
    field_simp [(sub_pos.mpr hr1).ne']
    ring
  have hscaled := ha.mul_left (r^(N+1))
  have hterm (i : ℕ) :
      ‖(coeff (N+1+i) : ℝ)*r^(N+1+i)‖ = r^(N+1)*(a i*r^i) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hr _), pow_add]
    dsimp only [a]
    ring
  exact (by
    rw [← Real.norm_eq_abs]
    refine (tsum_of_norm_bounded hscaled.hasSum (fun i => (hterm i).le)).trans ?_
    rw [tsum_mul_left]
    have hp := mul_le_mul_of_nonneg_left h2 (pow_nonneg hr.le (N+1))
    convert hp using 1
    ring)

#print axioms theta_tail_abs

/-- Exact endpoint rule used to bound one bin of positive prefix weights. -/
theorem geometric_bin (s : Finset ℕ) (p : ℕ → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {lo hi : ℕ} (hp : ∀ j ∈ s, 0 ≤ p j)
    (hj : ∀ j ∈ s, lo ≤ j ∧ j ≤ hi) :
    r^hi * (∑ j ∈ s, p j) ≤ (∑ j ∈ s, p j*r^j) ∧
      (∑ j ∈ s, p j*r^j) ≤ r^lo * (∑ j ∈ s, p j) := by
  simp only [Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro j h
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr1 (hj j h).2) (hp j h)
  · apply Finset.sum_le_sum
    intro j h
    rw [mul_comm (r^lo)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr1 (hj j h).1) (hp j h)

#print axioms geometric_bin

end QuarticKernel
