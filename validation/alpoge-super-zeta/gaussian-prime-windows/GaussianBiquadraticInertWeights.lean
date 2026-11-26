import GaussianConductorResidue

/-! Rational-prime weights for the lift from the Gaussian base to
`ℚ(i, √D)`. The field and Frobenius identification is explained in
`gaussian-biquadratic-class-character.md`. -/

namespace QuarticModel

open QuarticDualArithmetic

theorem gaussian_discriminant_coprime_star :
    IsCoprime gaussianDiscriminant (star gaussianDiscriminant) := by
  refine ⟨⟨-1779499, -4161725⟩, ⟨3265656, 3134017⟩, ?_⟩
  decide +kernel

theorem gaussian_discriminant_norm_mod_eight : modulus % 8 = 1 := by
  decide +kernel

set_option maxRecDepth 60000 in
theorem prime_dvd_gaussian_discriminant_norm_mod_four {p : ℕ} (hp : p.Prime)
    (h : p ∣ modulus) : p % 4 = 1 := by
  change p ∣ (41 * 457) * 1414835497 at h
  rcases hp.dvd_mul.mp h with hleft | hright
  · rcases hp.dvd_mul.mp hleft with h₄₁ | h₄₅₇
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41)).mp h₄₁
      norm_num [he]
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 457)).mp h₄₅₇
      norm_num [he]
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1414835497)).mp hright
    norm_num [he]

#print axioms gaussian_discriminant_coprime_star
#print axioms gaussian_discriminant_norm_mod_eight
#print axioms prime_dvd_gaussian_discriminant_norm_mod_four

end QuarticModel

namespace AlpogeSuperZeta

open QuarticModel

noncomputable section

/-- Away from the bad primes, the degree-one weight for the relative
inert primes of the biquadratic base. Split primes of that base have
two lifts of each of the two Gaussian primes. -/
def biquadraticInertDegreeOneWeight (p : ℕ) : ℝ :=
  if p % 4 = 1 ∧ rationalNormSign p = 1 then 2 * archivedInertDegreeOneWeight p else 0

/-- The contribution of the mixed-sign primes, expressed with the two
rational quadratic characters. -/
def mixedQuadraticPrimeWeight (p : ℕ) : ℝ :=
  (1 + (ZMod.χ₄ (p : ZMod 4) : ℝ)) * (1 - (rationalNormSign p : ℝ)) / 2

theorem biquadraticInertDegreeOneWeight_add_mixed {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    biquadraticInertDegreeOneWeight p + mixedQuadraticPrimeWeight p =
      2 * archivedInertDegreeOneWeight p := by
  have hI := archivedInertDegreeOneWeight_of_good_prime hp hc
  by_cases h₁ : p % 4 = 1
  · by_cases hD : rationalNormSign p = 1
    · simp [biquadraticInertDegreeOneWeight, mixedQuadraticPrimeWeight, h₁, hD]
    · have hD' : rationalNormSign p = -1 := by
        have hχ : rationalNormSign p = 1 ∨ rationalNormSign p = -1 := by
          rw [← rationalNormSign_reciprocity p hp]
          exact legendreSym.eq_one_or_neg_one p (a := (26509772707289 : ℤ)) (by
            simpa only [Int.cast_ofNat] using norm_discriminant_ne_zero hc)
        exact hχ.resolve_left hD
      have ha : archivedGaussianPrimeWeight p = 0 := by
        by_contra hn
        exact hD ((archivedGaussianPrimeWeight_ne_zero_iff hp hc).mp hn).2
      rw [ZMod.χ₄_nat_one_mod_four h₁, ha] at hI
      rw [biquadraticInertDegreeOneWeight, if_neg (fun h => hD h.2),
        mixedQuadraticPrimeWeight, ZMod.χ₄_nat_one_mod_four h₁, hD']
      norm_num at hI ⊢
      linarith only [hI]
  · have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
    have h₃ : p % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four h₃, archivedGaussianPrimeWeight_inert h₃] at hI
    rw [biquadraticInertDegreeOneWeight, if_neg (fun h => h₁ h.1),
      mixedQuadraticPrimeWeight, ZMod.χ₄_nat_three_mod_four h₃]
    norm_num at hI ⊢
    exact hI

/-- Subtract the signed weight from the degree-one count of the other
imaginary quadratic base. The difference from the biquadratic count
is a rational quadratic term. -/
theorem cyclic_class_prime_weight {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    1 + (ZMod.χ₄ (p : ZMod 4) : ℝ) * (rationalNormSign p : ℝ) -
        archivedGaussianPrimeWeight p =
      biquadraticInertDegreeOneWeight p +
        (1 - (ZMod.χ₄ (p : ZMod 4) : ℝ)) * (1 - (rationalNormSign p : ℝ)) / 2 := by
  have hI := archivedInertDegreeOneWeight_of_good_prime hp hc
  have hA := biquadraticInertDegreeOneWeight_add_mixed hp hc
  unfold mixedQuadraticPrimeWeight at hA
  linarith only [hI, hA]

/-- The surviving degree-one inert weight is four on the negative
Gaussian class and zero on the other good prime classes. -/
theorem biquadraticInertDegreeOneWeight_eq_if {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    biquadraticInertDegreeOneWeight p = if archivedGaussianPrimeWeight p = -2 then 4 else 0 := by
  by_cases h : p % 4 = 1 ∧ rationalNormSign p = 1
  · have hI := archivedInertDegreeOneWeight_of_good_prime hp hc
    have ha := archivedGaussianPrimeWeight_sq hp hc
    rw [ZMod.χ₄_nat_one_mod_four h.1, h.2] at ha
    norm_num at ha
    have hprod : (archivedGaussianPrimeWeight p - 2) *
        (archivedGaussianPrimeWeight p + 2) = 0 := by nlinarith only [ha]
    rw [ZMod.χ₄_nat_one_mod_four h.1] at hI
    rcases mul_eq_zero.mp hprod with ha | ha
    · have hpos : archivedGaussianPrimeWeight p = 2 := by linarith
      rw [hpos] at hI
      rw [biquadraticInertDegreeOneWeight, if_pos h, hpos]
      norm_num at hI ⊢
      exact hI
    · have hneg : archivedGaussianPrimeWeight p = -2 := by linarith
      rw [hneg] at hI
      rw [biquadraticInertDegreeOneWeight, if_pos h, hneg]
      norm_num at hI ⊢
      exact hI
  · have ha : archivedGaussianPrimeWeight p = 0 := by
      by_contra hn
      exact h ((archivedGaussianPrimeWeight_ne_zero_iff hp hc).mp hn)
    simp [biquadraticInertDegreeOneWeight, h, ha]

/-- The same identity holds with any common weight on the good rational
primes, including the smoothed norm-cutoff weight. -/
theorem biquadratic_inert_weighted_sum (primes : Finset ℕ) (w : ℕ → ℝ)
    (h : ∀ p ∈ primes, p.Prime ∧ p ≠ 2 ∧ p.Coprime 26509772707289) :
    (∑ p ∈ primes, w p * biquadraticInertDegreeOneWeight p) +
      (∑ p ∈ primes, w p * mixedQuadraticPrimeWeight p) =
        2 * ∑ p ∈ primes, w p * archivedInertDegreeOneWeight p := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hprime, ht, hc⟩ := h p hp
  let : Fact p.Prime := ⟨hprime⟩
  rw [← mul_add, biquadraticInertDegreeOneWeight_add_mixed ht hc]
  ring

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem biquadratic_inert_weights_at_5_13_73 :
    biquadraticInertDegreeOneWeight 5 = 0 ∧
    biquadraticInertDegreeOneWeight 13 = 4 ∧
    biquadraticInertDegreeOneWeight 73 = 0 := by
  have hc₅ : Nat.Coprime 5 26509772707289 := by decide +kernel
  have hc₁₃ : Nat.Coprime 13 26509772707289 := by decide +kernel
  have hc₇₃ : Nat.Coprime 73 26509772707289 := by decide +kernel
  rcases archivedGaussianPrimeWeight_at_5_and_13 with ⟨h₅, h₁₃⟩
  have h₇₃ := archivedGaussianPrimeWeights_at_73.1
  rw [biquadraticInertDegreeOneWeight_eq_if (by decide) hc₅,
    biquadraticInertDegreeOneWeight_eq_if (by decide) hc₁₃,
    biquadraticInertDegreeOneWeight_eq_if (by decide) hc₇₃, h₅, h₁₃, h₇₃]
  norm_num

#print axioms biquadraticInertDegreeOneWeight_add_mixed
#print axioms cyclic_class_prime_weight
#print axioms biquadraticInertDegreeOneWeight_eq_if
#print axioms biquadratic_inert_weighted_sum
#print axioms biquadratic_inert_weights_at_5_13_73

end
end AlpogeSuperZeta
