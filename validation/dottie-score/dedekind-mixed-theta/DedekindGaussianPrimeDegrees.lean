import DedekindGaussianQuadratic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

namespace FieldTarget

set_option autoImplicit false

open Ideal NumberField

attribute [local instance] gaussianQuadratic_isCyclotomic

private theorem gaussianQuadratic_oddPrime_not_dvd_four (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have hpow : p ∣ (2 : ℕ)^2 := h
  have hdiv := (Fact.out : p.Prime).prime.dvd_of_dvd_pow hpow
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdiv)

private theorem gaussianQuadratic_order_mod_four (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) : orderOf (p : ZMod 4) = if p % 4 = 1 then 1 else 2 := by
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rw [← ZMod.natCast_mod p 4]
  rcases hcases with h | h
  · rw [h]
    simp
  · rw [h]
    have h3 : ((3 : ℕ) : ZMod 4) = -1 := by decide
    let _ : Nontrivial (ZMod 4) := ⟨⟨0, 1, by decide⟩⟩
    rw [h3, orderOf_neg_one, ringChar.eq (ZMod 4) 4]
    decide

/-- The rational prime two has one prime above it, with residue degree one. -/
theorem gaussianQuadratic_primesOver_two :
    (primesOver (span {(2 : ℤ)}) (𝓞 GaussianQuadraticField)).ncard = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclotomicExtension {(2 : ℕ)^(1+1)} ℚ GaussianQuadraticField := gaussianQuadratic_isCyclotomic
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow
    (p := 2) (k := 1) (K := GaussianQuadraticField)

theorem gaussianQuadratic_inertiaDegIn_two :
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 GaussianQuadraticField) = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclotomicExtension {(2 : ℕ)^(1+1)} ℚ GaussianQuadraticField := gaussianQuadratic_isCyclotomic
  exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow
    (p := 2) (k := 1) (K := GaussianQuadraticField)

/-- Odd rational primes have degree one if split and degree two if inert. -/
theorem gaussianQuadratic_oddPrime_inertiaDegIn (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 GaussianQuadraticField) = if p % 4 = 1 then 1 else 2 := by
  rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 4)
    (p := p) (K := GaussianQuadraticField) (gaussianQuadratic_oddPrime_not_dvd_four p hp)]
  exact gaussianQuadratic_order_mod_four p hp

/-- The actual Gaussian field has two primes above a split odd prime and one
above an inert odd prime. -/
theorem gaussianQuadratic_primesOver_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (primesOver (span {(p : ℤ)}) (𝓞 GaussianQuadraticField)).ncard = if p % 4 = 1 then 2 else 1 := by
  let K := GaussianQuadraticField
  let Q : Ideal ℤ := span {(p : ℤ)}
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ GaussianQuadraticField
  have hcount := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn Q (𝓞 K) Gal(K/ℚ)
  have he : Q.ramificationIdxIn (𝓞 K) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 4)
      (p := p) (K := GaussianQuadraticField) (gaussianQuadratic_oddPrime_not_dvd_four p hp)
  have hd : Q.inertiaDegIn (𝓞 K) = if p % 4 = 1 then 1 else 2 :=
    gaussianQuadratic_oddPrime_inertiaDegIn p hp
  have htot : Nat.totient 4 = 2 := by decide
  have hrank : Module.finrank ℚ K = 2 :=
    (IsCyclotomicExtension.Rat.finrank (k := 4) GaussianQuadraticField).trans htot
  rw [he, hd, one_mul, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, hrank] at hcount
  change (primesOver Q (𝓞 K)).ncard = _
  split_ifs at hcount ⊢ <;> omega

#check @gaussianQuadratic_primesOver_odd
#print axioms gaussianQuadratic_primesOver_two
#print axioms gaussianQuadratic_inertiaDegIn_two
#print axioms gaussianQuadratic_oddPrime_inertiaDegIn
#print axioms gaussianQuadratic_primesOver_odd

end FieldTarget
