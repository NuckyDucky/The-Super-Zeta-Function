import QuarticModel
import GoodPrime

namespace QuarticAt73

open NumberField Polynomial QuarticModel

theorem good_reduction : ¬ 73 ∣ RingOfIntegers.exponent theta :=
  QuarticCoefficient.goodPrime73 theta theta_generates minpoly_theta

/-- The actual coefficient in Mathlib's ideal-counting Dirichlet series for K. -/
theorem ideal_count : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 73} = 2 :=
  QuarticCoefficient.primeCoefficient_73 theta minpoly_theta good_reduction

/-- The element recovered from the quartic gives an integral square root of -1. -/
noncomputable def iIntegral : 𝓞 K :=
  ⟨gaussianI, (show IsIntegral ℤ gaussianI from
    ⟨X^2 + 1, by monicity; decide, by simp [gaussianI_sq]⟩)⟩

private theorem iIntegral_sq : iIntegral^2 = -1 := by
  apply Subtype.ext
  exact gaussianI_sq

private theorem theta_sq_integral : theta^2 = -5045155 + 1027708*iIntegral := by
  apply Subtype.ext
  exact theta_sq

/-- Every degree-one residue map selects the *same* Gaussian prime. The two
    degrees of freedom are the two lifts of its square root. -/
theorem residue_pair (φ : 𝓞 K →+* ZMod 73) :
    φ iIntegral = 46 ∧ (φ theta = 9 ∨ φ theta = 64) := by
  have hi := congrArg φ iIntegral_sq
  have ht := congrArg φ theta_sq_integral
  simp only [map_pow, map_neg, map_one, map_ofNat, map_add, map_mul] at hi ht
  have hj : ∀ j : ZMod 73, j^2 = -1 → j = 27 ∨ j = 46 := by decide
  rcases hj _ hi with h | h
  · rw [h] at ht
    exact False.elim ((by decide : ∀ t : ZMod 73, t^2 ≠ -5045155 + 1027708*27) _ ht)
  · rw [h] at ht
    exact ⟨h, (by decide : ∀ t : ZMod 73, t^2 = -5045155 + 1027708*46 →
      t = 9 ∨ t = 64) _ ht⟩

/-- Reduction at the Gaussian primes (3+8i) and (3-8i), respectively.
    The nonsquare 34 has no square root in the residue field.
    The square 8 has the two exhibited roots. -/
theorem signed_residues :
    let δ (j : ZMod 73) := -5045155 + 1027708*j
    (3 + 8*(27 : ZMod 73) = 0 ∧ 3 - 8*(46 : ZMod 73) = 0) ∧
    δ 27 = 34 ∧ (∀ t : ZMod 73, t^2 ≠ δ 27) ∧
    δ 46 = 8 ∧ (∀ t : ZMod 73, t^2 = δ 46 ↔ t = 9 ∨ t = 64) := by decide

#print axioms good_reduction
#print axioms ideal_count
#print axioms residue_pair
#print axioms signed_residues

end QuarticAt73
