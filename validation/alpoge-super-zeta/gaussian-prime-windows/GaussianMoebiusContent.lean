import ArchivedGaussianPrimeWeights
import GaussianSeventhFreeMellin

/-! Local factors of the Gaussian ideal Möbius sum, with independent
variables for the rational content and the primitive ideal norm. -/

namespace AlpogeSuperZeta

open QuarticModel Finset
open scoped Classical

noncomputable section

/-- The rational character of the content of a squarefree Gaussian ideal. -/
def archivedGaussianContentSign (p : ℕ) : ℤ :=
  ZMod.χ₄ (p : ZMod 4) * rationalNormSign p

/-- The rational content and the primitive part occupy separate variables.
The choice of both primes over a split rational prime belongs to the content. -/
def archivedGaussianContentEulerFactor (p : ℕ) (u v : ℂ) : ℂ :=
  1 + (archivedGaussianContentSign p : ℂ) * u - (archivedGaussianPrimeWeight p : ℂ) * v

private theorem archivedIdealCharacter_rational (p : ℕ) :
    archivedIdealCharacter (Ideal.span ({(p : GaussianInt)} : Set GaussianInt)) =
      rationalNormSign p := by
  rw [archivedIdealCharacter_span]
  simp [archivedGaussianSign_eq_legendre, rationalNormSign]

/-- The diagonal specializes to the reciprocal of the actual signed Gaussian
local Euler factor. The squared variable records the norm of a rational ideal. -/
theorem archivedGaussianContentEulerFactor_diagonal (p : ℕ) [Fact p.Prime] (v : ℂ) :
    archivedGaussianContentEulerFactor p (v ^ 2) v =
      ∏ I ∈ gaussianPrimesAbove p, (1 - (archivedIdealCharacter I : ℂ) * v ^ I.inertiaDeg ℤ) := by
  have hp : p.Prime := Fact.out
  have hW : archivedGaussianPrimeWeight p = archivedGaussianPrimePowerWeight p 1 := by
    simpa only [pow_one] using archivedGaussianPrimeWeight_prime_power hp (j := 1) one_ne_zero
  rw [archivedGaussianContentEulerFactor, hW, archivedGaussianPrimePowerWeight,
    archivedGaussianContentSign]
  by_cases hp₂ : p = 2
  · subst p
    rw [dyadic_gaussian_prime, prod_singleton, sum_singleton, dyadic_gaussian_prime_degree]
    have hχ : ZMod.χ₄ (2 : ZMod 4) = 0 := by decide +kernel
    simp [hχ]
  · have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp₂
    have hp₄ : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp₄ with hp₁ | hp₃
    · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
      have hpos : r ^ 2 = -1 := by rw [pow_two, ← hr]
      have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
      have hs := split_gaussian_primes hp₂ r hpos hneg
      have ha : gaussianPrimeAt r hpos ∈ gaussianPrimesAbove p := by simp [hs]
      have hb : gaussianPrimeAt (-r) hneg ∈ gaussianPrimesAbove p := by simp [hs]
      have hne : gaussianPrimeAt r hpos ∉ ({gaussianPrimeAt (-r) hneg} : Finset _) := by
        simpa only [mem_singleton] using gaussianPrimeAt_distinct hp₂ r hpos
      have hprod : archivedIdealCharacter (gaussianPrimeAt r hpos) *
          archivedIdealCharacter (gaussianPrimeAt (-r) hneg) = rationalNormSign p := by
        rw [← map_mul, gaussianPrimeAt_product hp₂ r hpos, archivedIdealCharacter_rational]
      rw [hs, prod_insert hne, prod_singleton, sum_insert hne, sum_singleton,
        primeAt_degree r hpos ha, primeAt_degree (-r) hneg hb,
        ZMod.χ₄_nat_one_mod_four hp₁, one_mul, ← hprod]
      simp
      ring
    · rw [inert_gaussian_primes hp₃, prod_singleton, sum_singleton,
        inert_gaussian_prime_degree hp₃, ZMod.χ₄_nat_three_mod_four hp₃,
        archivedIdealCharacter_rational]
      have hd : ¬ 2 ∣ (1 : ℕ) := by decide +kernel
      simp [hd, sub_eq_add_neg]

/-- Comparing with separate rational and Gaussian Euler factors leaves
only a square in the norm variable or a mixed term. -/
theorem archivedGaussianContentEulerFactor_sub_product (p : ℕ) (u v : ℂ) :
    let c : ℂ := archivedGaussianContentSign p
    let a : ℂ := archivedGaussianPrimeWeight p
    archivedGaussianContentEulerFactor p u v -
        (1 + c * u) * archivedGaussianContentEulerFactor p (v ^ 2) v =
      a * c * u * v - c * v ^ 2 - c ^ 2 * u * v ^ 2 := by
  dsimp only [archivedGaussianContentEulerFactor]
  ring

private theorem archivedGaussianContentSign_norm_le_one (p : ℕ) :
    ‖(archivedGaussianContentSign p : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
    archivedGaussianContentSign, Int.cast_mul, abs_mul]
  have hR := archivedIdealCharacter_abs_le_one (Ideal.span ({(p : GaussianInt)} : Set GaussianInt))
  rw [archivedIdealCharacter_rational] at hR
  have h₄ : |(ZMod.χ₄ (p : ZMod 4) : ℝ)| ≤ 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> norm_num
  exact (mul_le_mul_of_nonneg_right h₄ (abs_nonneg _)).trans (by simpa using hR)

/-- The mixed Euler correction is summable on the part of the two-variable
plane where the square term and the mixed term are summable. -/
theorem archivedGaussianContentEulerFactor_sub_product_norm (p : ℕ) (u v : ℂ) :
    ‖archivedGaussianContentEulerFactor p u v -
        (1 + (archivedGaussianContentSign p : ℂ) * u) *
          archivedGaussianContentEulerFactor p (v ^ 2) v‖ ≤
      2 * ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖u‖ * ‖v‖ ^ 2 := by
  let c : ℂ := archivedGaussianContentSign p
  let a : ℂ := archivedGaussianPrimeWeight p
  have ha : ‖a‖ ≤ 2 := by
    simpa only [a, Complex.norm_real, Real.norm_eq_abs] using
      archivedGaussianPrimeWeight_abs_le_two p
  have hc : ‖c‖ ≤ 1 := archivedGaussianContentSign_norm_le_one p
  rw [archivedGaussianContentEulerFactor_sub_product]
  change ‖a * c * u * v - c * v ^ 2 - c ^ 2 * u * v ^ 2‖ ≤ _
  calc
    _ ≤ ‖a * c * u * v - c * v ^ 2‖ + ‖c ^ 2 * u * v ^ 2‖ := norm_sub_le _ _
    _ ≤ (‖a * c * u * v‖ + ‖c * v ^ 2‖) + ‖c ^ 2 * u * v ^ 2‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = (‖a‖ * ‖c‖ * ‖u‖ * ‖v‖ + ‖c‖ * ‖v‖ ^ 2) + ‖c‖ ^ 2 * ‖u‖ * ‖v‖ ^ 2 := by
      simp only [norm_mul, norm_pow]
    _ ≤ _ := by
      calc
        _ ≤ (2 * 1 * ‖u‖ * ‖v‖ + 1 * ‖v‖ ^ 2) + (1 : ℝ) ^ 2 * ‖u‖ * ‖v‖ ^ 2 := by
          gcongr
        _ = _ := by simp

/-- These strict contour coordinates give an exponent below one half
for primitive ideal norms up to the square root of the scale. -/
theorem archivedGaussianContent_contour_coordinates :
    let v : ℝ := 1251 / 10000
    let w : ℝ := 8734 / 10000
    1 / 4 < 2 * v ∧ archivedGaussianKnownBoundary < w ∧ 1 / 2 < w ∧
      1 < 2 * v + w ∧ 0 < w - v ∧ v + (w - v) / 2 = 1997 / 4000 ∧
      (1997 / 4000 : ℝ) < 1 / 2 := by
  norm_num [archivedGaussianKnownBoundary]

#print axioms archivedGaussianContentEulerFactor_diagonal
#print axioms archivedGaussianContentEulerFactor_sub_product
#print axioms archivedGaussianContentEulerFactor_sub_product_norm
#print axioms archivedGaussianContent_contour_coordinates

end
end AlpogeSuperZeta
