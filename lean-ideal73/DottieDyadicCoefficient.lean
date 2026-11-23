import ArchivedQuarticLatticeCoefficients
import Mathlib.Data.Nat.Factorization.Basic

/-! Doubling a norm preserves the original signed Gaussian coefficient. -/

namespace QuarticModel

open PowerSeries
open scoped Classical

private theorem signedIdealNormSum_two_pow (k : ℕ) : signedIdealNormSum (2 ^ k) = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have prime_eq (I : ↥(gaussianPrimesAbove 2)) :
      I.val = Ideal.span {(⟨1, 1⟩ : GaussianInt)} := by
    simpa only [dyadic_gaussian_prime, Finset.mem_singleton] using I.property
  have sign_eq (I : ↥(gaussianPrimesAbove 2)) : archivedIdealCharacter I.val = 1 := by
    rw [prime_eq I, archivedIdealCharacter_span]
    norm_num [archivedGaussianSign]
  have degree_eq (I : ↥(gaussianPrimesAbove 2)) : I.val.inertiaDeg ℤ = 1 := by
    rw [prime_eq I, dyadic_gaussian_prime_degree]
  have card_eq : Fintype.card ↥(gaussianPrimesAbove 2) = 1 := by
    rw [Fintype.card_coe, dyadic_gaussian_prime, Finset.card_singleton]
  have local_eq : signedLocalEulerSeries 2 = weightedGeometricAtDegree 1 1 := by
    simp only [signedLocalEulerSeries, sign_eq, degree_eq, Int.cast_one, Finset.prod_const,
      Finset.card_univ, card_eq, pow_one]
  rw [signedIdealNormSum_primePower, local_eq, coeff_weightedGeometricAtDegree 1 one_ne_zero]
  simp

/-- Every signed Gaussian norm coefficient equals the coefficient at twice its norm. -/
theorem archivedLatticeCoeff_two_mul (n : ℕ) :
    archivedLatticeCoeff (2 * n) = archivedLatticeCoeff n := by
  by_cases hn : n = 0
  · simp [hn]
  let k := n.factorization 2
  let m := ordCompl[2] n
  have decompose : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have coprime : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hn
  have same_sum (j : ℕ) : signedIdealNormSum (2 ^ j * m) = signedIdealNormSum m := by
    rw [signedIdealNormSum_mul_of_coprime (coprime.pow_left j), signedIdealNormSum_two_pow, one_mul]
  have doubled : 2 * n = 2 ^ (k + 1) * m := by
    rw [pow_succ', mul_assoc, decompose]
  have h₂n : 2 * n ≠ 0 := mul_ne_zero (by decide) hn
  have equality : (archivedLatticeCoeff (2 * n) : ℂ) = (archivedLatticeCoeff n : ℂ) := by
    rw [archivedLatticeCoeff_eq_signedIdealNormSum _ h₂n,
      archivedLatticeCoeff_eq_signedIdealNormSum _ hn]
    calc
      signedIdealNormSum (2 * n) = signedIdealNormSum (2 ^ (k + 1) * m) :=
        congrArg signedIdealNormSum doubled
      _ = signedIdealNormSum m := same_sum (k + 1)
      _ = signedIdealNormSum (2 ^ k * m) := (same_sum k).symm
      _ = signedIdealNormSum n := congrArg signedIdealNormSum decompose
  exact_mod_cast equality

#print axioms archivedLatticeCoeff_two_mul

end QuarticModel
