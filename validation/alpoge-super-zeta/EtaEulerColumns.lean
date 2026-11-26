import EtaEulerSum

/-! Collect the Euler coefficients using a single binomial row. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.EtaMellin

def binomialPrefix (n j : ℕ) : ℕ := ∑ i ∈ Finset.range (j+1), n.choose i

theorem binomialPrefix_append (n j : ℕ) :
    binomialPrefix n (j+1) = binomialPrefix n j + n.choose (j+1) := by
  exact Finset.sum_range_succ ..

private theorem binomialPrefix_zero (j : ℕ) : binomialPrefix 0 j = 1 := by
  induction j with
  | zero => simp [binomialPrefix]
  | succ j ih =>
    rw [binomialPrefix_append, ih, Nat.choose_eq_zero_of_lt (Nat.succ_pos _), add_zero]

private theorem binomialPrefix_succ (n j : ℕ) :
    binomialPrefix (n+1) j + n.choose j = 2*binomialPrefix n j := by
  induction j with
  | zero => simp [binomialPrefix]
  | succ j ih =>
    rw [binomialPrefix_append (n+1), binomialPrefix_append n, Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega

def columnWeight (n j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (k.choose j:ℝ)/2^(k+1)

theorem columnWeight_eq (n j : ℕ) :
    columnWeight n j = 1-(binomialPrefix n j:ℝ)/2^n := by
  induction n with
  | zero => simp [columnWeight, binomialPrefix_zero]
  | succ n ih =>
    have hp := (show
        (binomialPrefix (n+1) j:ℝ) + (n.choose j:ℝ) = 2*(binomialPrefix n j:ℝ) by
      exact_mod_cast binomialPrefix_succ n j)
    have he : (binomialPrefix (n+1) j:ℝ) =
        2*(binomialPrefix n j:ℝ)-(n.choose j:ℝ) := eq_sub_of_add_eq hp
    change columnWeight (n+1) j = _
    rw [show columnWeight (n+1) j = columnWeight n j+(n.choose j:ℝ)/2^(n+1) by
      unfold columnWeight; rw [Finset.sum_range_succ], ih, he, pow_succ (2:ℝ)]
    ring

theorem euler_sum_by_columns (n : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1), binomialWeight k j * f j) =
      ∑ j ∈ Finset.range n, ((-1:ℂ)^j * (columnWeight n j:ℂ)) * f j := by
  have extend (k : ℕ) (hk : k ∈ Finset.range n) :
      (∑ j ∈ Finset.range (k+1), binomialWeight k j * f j) =
        ∑ j ∈ Finset.range n, binomialWeight k j * f j := by
    refine Finset.sum_subset (Finset.range_mono (Finset.mem_range.mp hk)) ?_
    intro j _ hj
    have h : k < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    unfold binomialWeight
    rw [Nat.choose_eq_zero_of_lt h]
    simp
  simp only [Finset.sum_congr rfl extend]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [columnWeight, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [binomialWeight, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_div]
  ring

#print axioms columnWeight_eq
#print axioms euler_sum_by_columns

end DottieOriented.NativeSpectrum.EtaMellin
end
