import GaussianCommonDivisorPowers
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Möbius inversion of the prime-power containment tests. The input
to the inversion is the exact common divisor ideal, and the output
keeps only the shifted prime-power index. -/

namespace AlpogeSuperZeta

open QuarticModel Finset
open scoped ArithmeticFunction.Moebius Classical

private theorem moebius_count_of_shifted_multiples (q p B : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ v ∈ n.divisorsAntidiagonal, μ v.1 *
      (∑ j ∈ range B, if q * p ^ j ∣ v.2 then (1 : ℤ) else 0)) =
        ∑ j ∈ range B, if n = q * p ^ j then 1 else 0 := by
  let f (d : ℕ) : ℤ := ∑ j ∈ range B, if d = q * p ^ j then 1 else 0
  let g (d : ℕ) : ℤ := ∑ j ∈ range B, if q * p ^ j ∣ d then 1 else 0
  have h (d : ℕ) (hd : 0 < d) : ∑ e ∈ d.divisors, f e = g d := by
    dsimp [f, g]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => by simp [Nat.mem_divisors, hd.ne']
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp h) n hn

/-- Up to any power cutoff, the Möbius transform of the exact local
prime-power containment counts isolates the shifted indices. -/
theorem gaussianCommonDivisor_moebius_prime_powers {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : p.Coprime 26509772707289) (I : ↥(gaussianPrimesAbove p))
    (hneg : archivedIdealCharacter I.val = -1) (B : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ v ∈ n.divisorsAntidiagonal, μ v.1 *
      (∑ j ∈ range B, if gaussianCommonDivisorIdeal v.2 ≤ I.val ^ (j + 1)
        then (1 : ℤ) else 0)) =
      ∑ j ∈ range B, if n = (I.val.absNorm + 1) * p ^ j then 1 else 0 := by
  calc
    _ = ∑ v ∈ n.divisorsAntidiagonal, μ v.1 *
      (∑ j ∈ range B, if (I.val.absNorm + 1) * p ^ j ∣ v.2 then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro v hv
      have hv' := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)
      congr 1
      apply sum_congr rfl
      intro j _
      rw [gaussianCommonDivisor_le_prime_pow_iff hp hD I hv' (Nat.succ_pos j)]
      simp only [Nat.succ_sub_one, hneg, true_and]
    _ = _ := moebius_count_of_shifted_multiples _ _ B hn

#print axioms gaussianCommonDivisor_moebius_prime_powers

end AlpogeSuperZeta
