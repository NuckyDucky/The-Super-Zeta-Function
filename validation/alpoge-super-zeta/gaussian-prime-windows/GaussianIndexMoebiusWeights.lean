import GaussianIndexWeights
import GaussianCommonDivisorMoebius
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! The prime weights used by the shifted index ramp are exactly the
norm-weighted Möbius coefficients of the determinant common divisors. -/

namespace AlpogeSuperZeta

open Finset QuarticModel
open scoped ArithmeticFunction.Moebius Classical

noncomputable section

/-- At every good prime, grouping the exact Möbius coefficients by
residue degree produces the two weighted index families. -/
theorem gaussianIndex_weighted_moebius_at_prime {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : p.Coprime 26509772707289) (B : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ I ∈ gaussianPrimesAbove p, if archivedIdealCharacter I = -1 then
      Real.log I.absNorm *
        (((∑ v ∈ n.divisorsAntidiagonal, μ v.1 *
          (∑ j ∈ range B, if gaussianCommonDivisorIdeal v.2 ≤ I ^ (j + 1)
            then (1 : ℤ) else 0)) : ℤ) : ℝ) else 0) =
      archivedInertIndexWeight p 1 *
        (∑ j ∈ range B, if n = (p + 1) * p ^ j then (1 : ℝ) else 0) +
      archivedInertIndexWeight p 2 *
        (∑ j ∈ range B, if n = (p ^ 2 + 1) * p ^ j then (1 : ℝ) else 0) := by
  have hgood : archivedGoodIndexPrime p := ⟨Fact.out, hp, hD⟩
  simp only [archivedInertIndexWeight, if_pos hgood, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun I hi => ?_
  by_cases hneg : archivedIdealCharacter I = -1
  · have hm := gaussianCommonDivisor_moebius_prime_powers hp hD ⟨I, hi⟩ hneg B hn
    change (∑ v ∈ n.divisorsAntidiagonal, μ v.1 *
      (∑ j ∈ range B, if gaussianCommonDivisorIdeal v.2 ≤ I ^ (j + 1)
        then (1 : ℤ) else 0)) = _ at hm
    let hprime : I.IsPrime := ((mem_gaussianPrimesAbove p).mp hi).1
    let hover : I.LiesOver (Ideal.span {(p : ℤ)}) := ((mem_gaussianPrimesAbove p).mp hi).2
    have hN := (Ideal.pow_inertiaDeg p I).symm
    rw [if_pos hneg, hm, hN, Nat.cast_pow, Real.log_pow]
    push_cast
    rcases (gaussianIndexPrime_shape hp).2 I hi with h | h <;> simp [hneg, h, mul_comm]
  · simp [hneg]

#print axioms gaussianIndex_weighted_moebius_at_prime

end
end AlpogeSuperZeta
