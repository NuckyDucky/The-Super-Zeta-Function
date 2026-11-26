import GaussianHermitePrimePolynomial
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! Coefficient sizes forced by matching distinct monomials modulo the shell primes. -/

namespace AlpogeSuperZeta

open Finset Polynomial

/-- An active coefficient is nonzero at its own prime and divisible by all
the other primes, even when the monomial indices are reindexed. -/
theorem monomialReductions_coefficient_bound (P : ℤ[X]) (c : ℤ) (S : Finset ℕ)
    (degree : ℕ → ℕ) (hprime : ∀ q ∈ S, q.Prime)
    (hdegree : Set.InjOn degree (↑S : Set ℕ))
    (hmap : ∀ q ∈ S, P.map (Int.castRingHom (ZMod q)) = C (c : ZMod q) * X ^ degree q)
    {p : ℕ} (hp : p ∈ S) (hc : (c : ZMod p) ≠ 0) :
    (∏ q ∈ S.erase p, q) ≤ (P.coeff (degree p)).natAbs := by
  have hself : (P.coeff (degree p) : ZMod p) = (c : ZMod p) := by
    simpa only [coeff_map, Int.coe_castRingHom, coeff_C_mul, coeff_X_pow_self, mul_one] using
      congrArg (fun Q : (ZMod p)[X] => Q.coeff (degree p)) (hmap p hp)
  have hn : P.coeff (degree p) ≠ 0 := by
    intro hz
    exact hc (by simpa [hz] using hself.symm)
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr hn) ?_
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hq r hr hqr
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (hprime q (mem_of_mem_erase hq)) (hprime r (mem_of_mem_erase hr))).mpr hqr)
  · intro q hq
    have hq' := mem_of_mem_erase hq
    have hneq : degree p ≠ degree q :=
      fun h => (ne_of_mem_erase hq) (hdegree hp hq' h).symm
    have hzero : (P.coeff (degree p) : ZMod q) = 0 := by
      simpa only [coeff_map, Int.coe_castRingHom, coeff_C_mul, coeff_X_pow, if_neg hneq, mul_zero] using
        congrArg (fun Q : (ZMod q)[X] => Q.coeff (degree p)) (hmap q hq')
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd

/-- The same lower bound holds for the actual integer Hermite polynomial,
on the whole prime interval or any subset. -/
theorem hermitePrimePolynomial_coefficient_bound {m : ℕ} (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ m ≤ q ∧ q < 2 * m)
    {p : ℕ} (hp : p ∈ S) :
    (∏ q ∈ S.erase p, q) ≤ ((hermitePrimePolynomial m).coeff p).natAbs := by
  refine monomialReductions_coefficient_bound (hermitePrimePolynomial m) (hermitePrimeScale m)
    S id (fun q hq => (hS q hq).1)
    (fun _ _ _ _ h => h) ?_ hp ?_
  · intro q hq
    obtain ⟨hprime, hlo, hhi⟩ := hS q hq
    let : Fact q.Prime := ⟨hprime⟩
    exact hermitePrimePolynomial_mod_prime (K := ZMod q) hprime hlo hhi
  · obtain ⟨hprime, hlo, hhi⟩ := hS p hp
    let : Fact p.Prime := ⟨hprime⟩
    have hn : (((m - 1).factorial : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hd := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h
      have hle := hprime.dvd_factorial.mp hd
      omega
    simpa only [hermitePrimeScale, Int.cast_pow, Int.cast_natCast] using pow_ne_zero 2 hn

#print axioms monomialReductions_coefficient_bound
#print axioms hermitePrimePolynomial_coefficient_bound

end AlpogeSuperZeta
