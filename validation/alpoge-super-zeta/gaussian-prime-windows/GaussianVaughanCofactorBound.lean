import GaussianMoebiusPairContent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Control the actual reciprocal Gaussian coefficients used for the
short cofactor sum. The finitely many small primes cost a fixed factor. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel
open scoped Classical

noncomputable section

private def fromPrimePowers (A : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p j => A (p ^ j)), by simp⟩

private theorem fromPrimePowers_multiplicative (A : ArithmeticFunction ℂ) :
    (fromPrimePowers A).IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [fromPrimePowers], ?_⟩
  intro m n hm hn hmn
  simp only [fromPrimePowers, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
    if_neg (mul_ne_zero hm hn), Nat.factorization_mul_of_coprime hmn]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors _

private theorem fromPrimePowers_apply_pow {A : ArithmeticFunction ℂ} (hA : A 1 = 1)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    fromPrimePowers A (p ^ j) = A (p ^ j) := by
  simp [fromPrimePowers, hp.ne_zero, Nat.Prime.factorization_pow hp,
    Finsupp.prod_single_index _, hA]

/-- The archived reciprocal sequence is multiplicative. Its local reciprocal
coefficients uniquely reconstruct the original inverse under convolution. -/
theorem archivedGaussianMoebius_multiplicative :
    archivedGaussianMoebiusCoefficients.IsMultiplicative := by
  let A := archivedGaussianMoebiusCoefficients
  let B := signedIdealCoefficients
  have hA : A 1 = 1 := by
    simpa [A] using archivedGaussianMoebius_ratio_prime_power Nat.prime_two 0
  have hAB : A * B = 1 := archivedGaussianMoebius_mul_signed
  have hE : fromPrimePowers A * B = 1 := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
      ((fromPrimePowers_multiplicative A).mul signedIdealCoefficients_multiplicative)
      _ isMultiplicative_one).mpr
    intro p j hp
    rw [← hAB, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro pair hpair
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp
      (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hpair))
    rw [hi, fromPrimePowers_apply_pow hA hp]
  have hEq : A = fromPrimePowers A := by
    calc
      A = A * (fromPrimePowers A * B) := by rw [hE, mul_one]
      _ = fromPrimePowers A * (A * B) := by ac_rfl
      _ = _ := by rw [hAB, mul_one]
  rw [show archivedGaussianMoebiusCoefficients = fromPrimePowers A from hEq]
  exact fromPrimePowers_multiplicative A

private theorem contentSign_norm_le_one (p : ℕ) :
    ‖(archivedGaussianContentSign p : ℂ)‖ ≤ 1 := by
  have hC : (archivedGaussianContentSign p : ℂ) ^ 3 =
      (archivedGaussianContentSign p : ℂ) := by
    exact_mod_cast archivedGaussianContentSign_cube p
  have hN : ‖(archivedGaussianContentSign p : ℂ)‖ ^ 3 =
      ‖(archivedGaussianContentSign p : ℂ)‖ := by simpa only [norm_pow] using congrArg norm hC
  by_contra! h
  have h₂ : 1 < ‖(archivedGaussianContentSign p : ℂ)‖ ^ 2 := one_lt_pow₀ h (by norm_num)
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ] at hN
  nlinarith [mul_pos (sub_pos.mpr h₂) (zero_lt_one.trans h)]

private theorem moebius_prime_power_norm_le_two {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ‖archivedGaussianMoebiusCoefficients (p ^ j)‖ ≤ 2 := by
  rw [archivedGaussianMoebius_ratio_prime_power hp]
  split_ifs with h₀ h₁ h₂
  · norm_num
  · simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using
      archivedGaussianPrimeWeight_abs_le_two p
  · exact (contentSign_norm_le_one p).trans (by norm_num)
  · norm_num

private theorem two_le_seven_rpow : (2 : ℝ) ≤ (7 : ℝ) ^ (3 / 8 : ℝ) := by
  have he : ((7 : ℝ) ^ (3 / 8 : ℝ)) ^ (8 : ℕ) = (7 : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
    norm_num [Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 7) _) (by decide : (8 : ℕ) ≠ 0)).mp
  rw [he]
  norm_num

private theorem moebius_prime_power_bound {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ‖archivedGaussianMoebiusCoefficients (p ^ j)‖ ≤
      (if p < 7 then (2 : ℝ) else 1) * ((p : ℝ) ^ j) ^ (3 / 8 : ℝ) := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hOne : 1 ≤ ((p : ℝ) ^ j) ^ (3 / 8 : ℝ) :=
    Real.one_le_rpow (one_le_pow₀ hp₁) (by norm_num)
  by_cases hSmall : p < 7
  · rw [if_pos hSmall]
    linarith [moebius_prime_power_norm_le_two hp j]
  rw [if_neg hSmall, one_mul]
  by_cases hj : j = 0
  · subst j
    have hA := archivedGaussianMoebius_ratio_prime_power hp 0
    simp only [pow_zero] at hA
    simp [hA]
  have h7 : (7 : ℝ) ≤ (p : ℝ) ^ j := by
    have h : 7 ≤ p ^ j := (le_of_not_gt hSmall).trans (Nat.le_pow (Nat.pos_of_ne_zero hj))
    exact_mod_cast h
  exact (moebius_prime_power_norm_le_two hp j).trans (two_le_seven_rpow.trans
    (Real.rpow_le_rpow (by norm_num) h7 (by norm_num)))

private theorem small_prime_mem {p : ℕ} (hp : p.Prime) (h : p < 7) :
    p ∈ ({2, 3, 5} : Finset ℕ) := by
  have he : ∀ q : Fin 7, (q : ℕ).Prime → (q : ℕ) ∈ ({2, 3, 5} : Finset ℕ) := by decide +kernel
  exact he ⟨p, h⟩ hp

/-- This single constant bounds the reciprocal coefficient after the
three-eighths power of the norm is taken out. -/
theorem archivedGaussianMoebius_three_eighths_bound {n : ℕ} (hn : n ≠ 0) :
    ‖archivedGaussianMoebiusCoefficients n‖ ≤ 8 * (n : ℝ) ^ (3 / 8 : ℝ) := by
  let s := n.primeFactors
  let f (p : ℕ) : ℝ := (p : ℝ) ^ (n.factorization p)
  let g (p : ℕ) : ℝ := if p < 7 then 2 else 1
  have hf (p : ℕ) : 0 ≤ f p := by dsimp [f]; positivity
  have hsmall : (s.filter fun p => p < 7) ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    exact small_prime_mem (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Finset.mem_filter.mp hp).2
  have hcard : (s.filter fun p => p < 7).card ≤ 3 := by
    simpa using Finset.card_le_card hsmall
  have hProd : (∏ p ∈ s, g p) ≤ 8 := by
    dsimp only [g]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℕ) := pow_le_pow_right₀ (by norm_num) hcard
      _ = 8 := by norm_num
  have hN : ∏ p ∈ s, f p = (n : ℝ) := by
    change (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ)
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  rw [IsMultiplicative.multiplicative_factorization _ archivedGaussianMoebius_multiplicative hn,
    Nat.prod_factorization_eq_prod_primeFactors, norm_prod]
  calc
    _ ≤ ∏ p ∈ s, g p * f p ^ (3 / 8 : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun p hp => moebius_prime_power_bound (Nat.prime_of_mem_primeFactors hp) _)
    _ = (∏ p ∈ s, g p) * (n : ℝ) ^ (3 / 8 : ℝ) := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow s f (fun p _ => hf p), hN]
    _ ≤ _ := mul_le_mul_of_nonneg_right hProd (by positivity)

#check archivedGaussianMoebius_three_eighths_bound
#print axioms archivedGaussianMoebius_multiplicative
#print axioms archivedGaussianMoebius_three_eighths_bound

end
end AlpogeSuperZeta
