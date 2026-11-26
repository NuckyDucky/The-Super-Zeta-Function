import GaussianBalancedMoebius
import GaussianPrimeSupport
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Split the actual signed Mangoldt sequence by divisor size and recover its
prime part by inversion over odd exponents. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Vaughan's identity uses only A * B = 1. The two pieces can be smooth cutoffs. -/
theorem gaussianVaughan_identity {R : Type*} [CommRing R]
    (A B L A₀ L₀ : R) (hAB : A * B = 1) :
    L = A₀ * (L * B) + L₀ - A₀ * B * L₀ + (A - A₀) * B * (L - L₀) := by
  calc
    L = (A * B) * L + L₀ - (A * B) * L₀ := by rw [hAB, one_mul, one_mul, add_sub_cancel_right]
    _ = _ := by ring

/-- Specialize the identity to the archived Gaussian weights. -/
theorem archivedGaussianMangoldt_vaughan (P Q : ArithmeticFunction ℂ) :
    let A := archivedGaussianMoebiusCoefficients
    let B := signedIdealCoefficients
    let L := archivedGaussianMangoldt
    let V : ArithmeticFunction ℂ := ⟨LSeries.logMul B, by simp [LSeries.logMul]⟩
    L = P * V + Q - P * B * Q + (A - P) * B * (L - Q) := by
  dsimp only
  have hprod : archivedGaussianMangoldt * signedIdealCoefficients =
      (⟨LSeries.logMul signedIdealCoefficients, by simp [LSeries.logMul]⟩ :
        ArithmeticFunction ℂ) := by
    ext n
    exact congrFun archivedGaussianMangoldt_convolution n
  rw [← hprod]
  exact gaussianVaughan_identity _ _ _ _ _ archivedGaussianMoebius_mul_signed

private theorem prime_iteration_moebius_sum (j : ℕ) :
    (∑ d ∈ j.divisors, (μ d : ℝ)) = if j = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f j)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, ArithmeticFunction.one_apply] using h

/-- Odd-exponent Möbius inversion applied to the actual prime-power weights,
including the primes at the conductor. The exponent of an iterated sum is
divided by its iteration count before reading the original coefficient. -/
theorem archivedGaussianOddIteration_inverts {p : ℕ} [Fact p.Prime] (j : ℕ) :
    (∑ d ∈ j.divisors, if Odd d ∧ Odd (j / d) then
      (μ d : ℝ) * archivedGaussianPrimeWeight (p ^ (j / d)) else 0) =
      if j = 1 then archivedGaussianPrimeWeight p else 0 := by
  by_cases hj : Odd j
  · calc
      _ = ∑ d ∈ j.divisors, (μ d : ℝ) * archivedGaussianPrimeWeight p := by
        apply sum_congr rfl
        intro d hd
        have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        have ho : Odd (d * (j / d)) := he.symm ▸ hj
        obtain ⟨hd₁, hd₂⟩ := Nat.odd_mul.mp ho
        rw [if_pos ⟨hd₁, hd₂⟩]
        obtain ⟨i, hi⟩ := hd₂
        rw [hi, archivedGaussianPrimeWeight_odd]
      _ = _ := by
        rw [← sum_mul, prime_iteration_moebius_sum]
        split_ifs <;> simp
  · have hn : j ≠ 1 := fun h => hj (h ▸ (by decide : Odd 1))
    rw [if_neg hn]
    refine sum_eq_zero fun d hd => ?_
    apply if_neg
    intro h
    have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    exact hj (he ▸ h.1.mul h.2)

/-- The odd-prime reading left after subtracting the even reading. -/
theorem archivedGaussianPrimeWeight_odd_iteration_15 :
    (∑ d ∈ (15 : ℕ).divisors, if Odd d ∧ Odd (15 / d) then
      (μ d : ℝ) * archivedGaussianPrimeWeight (5 ^ (15 / d)) else 0) = 0 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa only [show (15 : ℕ) ≠ 1 by decide, if_false] using
    (archivedGaussianOddIteration_inverts (p := 5) 15)

/-- If the product is at most X^(1+δ) and both inputs exceed the lower cut,
then both remaining norms lie within the advertised upper cut. -/
theorem gaussianVaughan_balanced_addresses {X a b δ : ℝ} (hX : 0 < X)
    (ha : X ^ (1 / 2 - δ) ≤ a) (hb : X ^ (1 / 2 - δ) ≤ b)
    (hab : a * b ≤ X ^ (1 + δ)) :
    a ≤ X ^ (1 / 2 + 2 * δ) ∧ b ≤ X ^ (1 / 2 + 2 * δ) := by
  have hp : 0 < X ^ (1 / 2 - δ) := Real.rpow_pos_of_pos hX _
  have he : X ^ (1 / 2 + 2 * δ) * X ^ (1 / 2 - δ) = X ^ (1 + δ) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  constructor
  · apply le_of_mul_le_mul_right _ hp
    rw [he]
    exact (mul_le_mul_of_nonneg_left hb (hp.le.trans ha)).trans hab
  · apply le_of_mul_le_mul_right _ hp
    rw [he, mul_comm b]
    exact (mul_le_mul_of_nonneg_right ha (hp.le.trans hb)).trans hab

/-- A single scale choice keeps the higher-power and shared-prime errors
below the intended square-root exponent. -/
theorem gaussianVaughan_error_exponents {ε : ℝ} (hε : 0 < ε) :
    ∃ δ τ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ 0 < τ ∧ τ < 1 ∧
      (1 / 2 - δ) * (1 - τ) + τ < 1 / 2 + ε / 2 ∧
      1 / 2 + 2 * δ < 1 / 2 + ε / 2 := by
  let δ := min (ε / 8) (1 / 16)
  have hpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hsmall : δ ≤ ε / 8 := min_le_left _ _
  have hmax : δ ≤ 1 / 16 := min_le_right _ _
  refine ⟨δ, δ, hpos, by linarith, hpos, by linarith, ?_, by linarith⟩
  nlinarith [sq_nonneg δ, mul_nonneg hpos.le (sub_nonneg.mpr hmax)]

#print axioms gaussianVaughan_identity
#print axioms archivedGaussianMangoldt_vaughan
#print axioms archivedGaussianOddIteration_inverts
#print axioms archivedGaussianPrimeWeight_odd_iteration_15
#print axioms gaussianVaughan_balanced_addresses
#print axioms gaussianVaughan_error_exponents

end
end AlpogeSuperZeta
