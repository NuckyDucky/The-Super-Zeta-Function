import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Finite Taylor polynomials for reflected exponential readings. -/

namespace FieldTarget

open scoped BigOperators

noncomputable section

/-- The even reading adds the two exponentials. The odd reading subtracts them. -/
def reflectedExpSign (odd : Bool) : ℤ :=
  if odd then -1 else 1

def reflectedExp (odd : Bool) (z : ℂ) : ℂ :=
  Complex.exp z + (reflectedExpSign odd : ℂ) * Complex.exp (-z)

/-- The coefficient multiplier is two in the selected parity and zero in the other. -/
def reflectedExpParity (odd : Bool) (k : ℕ) : ℤ :=
  1 + reflectedExpSign odd * (-1) ^ k

theorem reflectedExpParity_eq (odd : Bool) (k : ℕ) :
    reflectedExpParity odd k = if k % 2 = (if odd then 1 else 0) then 2 else 0 := by
  have hp (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, ih]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hs : (n + 1) % 2 = 1 := by omega
        simp [h, hs]
      · have hs : (n + 1) % 2 = 0 := by omega
        simp [h, hs]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
    cases odd <;> simp [reflectedExpParity, reflectedExpSign, hp, h]

/-- A sampled reading is a finite linear combination with real weights and nodes. -/
def reflectedExpSum {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (z : ℂ) : ℂ :=
  ∑ i ∈ s, (a i : ℂ) * reflectedExp odd ((r i : ℂ) * z)

/-- The Taylor coefficients are real, so the two parities can share the same
real moment calculation. -/
def reflectedExpCoefficient {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ s, a i * (reflectedExpParity odd k : ℝ) * r i ^ k / (k.factorial : ℝ)

def reflectedExpPolynomial {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, (reflectedExpCoefficient s a r odd k : ℂ) * z ^ k

private def expPartial (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, z ^ k / (k.factorial : ℂ)

private theorem expPair_partial_eq (odd : Bool) (N : ℕ) (z : ℂ) :
    expPartial N z + (reflectedExpSign odd : ℂ) * expPartial N (-z) =
      ∑ k ∈ Finset.range N, (reflectedExpParity odd k : ℂ) * z ^ k / (k.factorial : ℂ) := by
  unfold expPartial
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [reflectedExpParity, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one,
    Int.cast_pow]
  rw [← neg_one_mul z, mul_pow]
  ring

private theorem ofReal_coefficient {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (k : ℕ) :
    (reflectedExpCoefficient s a r odd k : ℂ) =
      ∑ i ∈ s, (a i : ℂ) * (reflectedExpParity odd k : ℂ) * (r i : ℂ) ^ k /
        (k.factorial : ℂ) := by
  unfold reflectedExpCoefficient
  change Complex.ofRealHom (∑ i ∈ s, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((a i * (reflectedExpParity odd k : ℝ) * r i ^ k / (k.factorial : ℝ) : ℝ) : ℂ) = _
  push_cast
  rfl

private theorem reflectedExpPolynomial_eq_sum {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (N : ℕ) (z : ℂ) :
    reflectedExpPolynomial s a r odd N z =
      ∑ i ∈ s, (a i : ℂ) * (expPartial N ((r i : ℂ) * z) +
        (reflectedExpSign odd : ℂ) * expPartial N (-((r i : ℂ) * z))) := by
  unfold reflectedExpPolynomial
  simp_rw [ofReal_coefficient, Finset.sum_mul, expPair_partial_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow]
  ring

/-- Both reflected exponentials share the usual Taylor remainder allowance. -/
private theorem reflectedExp_partial_error {T : ℝ} {N : ℕ}
    (hcut : T / (N.succ : ℝ) ≤ 1 / 2) (odd : Bool) {z : ℂ} (hz : ‖z‖ ≤ T) :
    ‖reflectedExp odd z -
        (expPartial N z + (reflectedExpSign odd : ℂ) * expPartial N (-z))‖ ≤
      4 * T ^ N / (N.factorial : ℝ) := by
  have norm_sign : ‖(reflectedExpSign odd : ℂ)‖ = 1 := by
    cases odd <;> simp [reflectedExpSign]
  have hcutP : ‖z‖ / (N.succ : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right hz (by positivity)).trans hcut
  have hcutM : ‖-z‖ / (N.succ : ℝ) ≤ 1 / 2 := by rw [norm_neg]; exact hcutP
  have hP := Complex.exp_bound' hcutP
  have hM := Complex.exp_bound' hcutM
  rw [norm_neg] at hM
  have hpow := pow_le_pow_left₀ (norm_nonneg z) hz N
  have hrem : ‖z‖ ^ N / (N.factorial : ℝ) * 2 ≤ T ^ N / (N.factorial : ℝ) * 2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by positivity)) (by norm_num)
  unfold reflectedExp
  rw [show Complex.exp z + (reflectedExpSign odd : ℂ) * Complex.exp (-z) -
      (expPartial N z + (reflectedExpSign odd : ℂ) * expPartial N (-z)) =
      (Complex.exp z - expPartial N z) + (reflectedExpSign odd : ℂ) *
        (Complex.exp (-z) - expPartial N (-z)) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_sign, one_mul]
  change ‖Complex.exp z - expPartial N z‖ + ‖Complex.exp (-z) - expPartial N (-z)‖ ≤ _
  have h₁ : ‖Complex.exp z - expPartial N z‖ ≤ T ^ N / (N.factorial : ℝ) * 2 :=
    hP.trans hrem
  have h₂ : ‖Complex.exp (-z) - expPartial N (-z)‖ ≤ T ^ N / (N.factorial : ℝ) * 2 :=
    hM.trans hrem
  calc
    _ ≤ T ^ N / (N.factorial : ℝ) * 2 + T ^ N / (N.factorial : ℝ) * 2 :=
      add_le_add h₁ h₂
    _ = _ := by ring

/-- The complex error of the shared Taylor polynomial is bounded by the absolute
mass of the weights times the error for one reflected pair. -/
theorem reflectedExpPolynomial_error_le {ι : Type*} (s : Finset ι) (a r : ι → ℝ)
    (odd : Bool) (N : ℕ) {z : ℂ} {T : ℝ}
    (hcut : T / (N.succ : ℝ) ≤ 1 / 2)
    (hz : ∀ i ∈ s, ‖(r i : ℂ) * z‖ ≤ T) :
    ‖reflectedExpSum s a r odd z - reflectedExpPolynomial s a r odd N z‖ ≤
      (∑ i ∈ s, |a i|) * (4 * T ^ N / (N.factorial : ℝ)) := by
  rw [reflectedExpSum, reflectedExpPolynomial_eq_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (reflectedExp_partial_error hcut odd (hz i hi)) (abs_nonneg _)

#print axioms reflectedExpParity_eq
#print axioms reflectedExpPolynomial_error_le

end

end FieldTarget

