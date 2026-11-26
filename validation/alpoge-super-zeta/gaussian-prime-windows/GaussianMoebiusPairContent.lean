import GaussianMoebiusCommonDivisor

/-! Separate the rational square parts of both coprime norms in the Gaussian
Möbius pair. The common-divisor label remains fixed. -/

namespace AlpogeSuperZeta

open QuarticModel

noncomputable section

/-- Separate the two rational square factors (u,v) from the two
primitive factors (x,y) at a fixed exponent of the common divisor. -/
def gaussianMoebiusPairContentFactor (a c : ℂ) (j : ℕ) (u v x y : ℂ) : ℂ :=
  match j with
  | 0 => 1 + c * (u + v) - a * (x + y)
  | 1 => a ^ 2 - a * c * (x + y)
  | 2 => c ^ 2
  | _ + 3 => 0

theorem gaussianMoebiusPairContent_diagonal (a c : ℂ) (j : ℕ) (x y : ℂ) :
    gaussianMoebiusPairContentFactor a c j (x ^ 2) (y ^ 2) x y =
      gaussianMoebiusPairFactor a c j x y := by
  rcases j with _ | _ | _ | j <;>
    simp only [gaussianMoebiusPairContentFactor, gaussianMoebiusPairFactor]
  ring

/-- The four-variable local polynomial of the actual inverse coefficients. -/
theorem archivedGaussianMoebius_pair_content {p : ℕ} (hp : p.Prime) (j : ℕ)
    (u v x y : ℂ) :
    let A := archivedGaussianMoebiusCoefficients
    A (p ^ j) ^ 2 + A (p ^ j) * A (p ^ (j + 1)) * (x + y) +
      A (p ^ j) * A (p ^ (j + 2)) * (u + v) =
      gaussianMoebiusPairContentFactor (archivedGaussianPrimeWeight p : ℂ)
        (archivedGaussianContentSign p : ℂ) j u v x y := by
  dsimp only
  simp only [archivedGaussianMoebius_ratio_prime_power hp]
  rcases j with _ | _ | _ | j
  · simp [gaussianMoebiusPairContentFactor, sub_eq_add_neg]
    ring
  · simp [gaussianMoebiusPairContentFactor, sub_eq_add_neg, neg_mul]
  · simp [gaussianMoebiusPairContentFactor]
  · simp [gaussianMoebiusPairContentFactor, show j + 3 ≠ 2 by omega,
      show j + 3 + 1 ≠ 2 by omega]

theorem archivedGaussianContentSign_cube (p : ℕ) :
    archivedGaussianContentSign p ^ 3 = archivedGaussianContentSign p := by
  have h (a : ℤ) (m : ℕ) : jacobiSym a m ^ 3 = jacobiSym a m := by
    rcases jacobiSym.trichotomy a m with hz | hp | hn
    · norm_num [hz]
    · norm_num [hp]
    · norm_num [hn]
  have hr : archivedGaussianSign (p : GaussianInt) = rationalNormSign p := by
    simp [archivedGaussianSign_eq_legendre, rationalNormSign]
  have hb : ZMod.χ₄ (p : ZMod 4) ^ 3 = ZMod.χ₄ (p : ZMod 4) := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> norm_num
  rw [archivedGaussianContentSign, mul_pow, hb, ← hr]
  simp only [archivedGaussianSign, mul_pow, h]

/-- The coprimality correction between the two square parts. After extracting
the quadratic term and both cubic terms, its numerator starts at order four. -/
theorem gaussianMoebius_rational_square_correction (c u v : ℂ) :
    (1 + c * (u + v)) * ((1 - c ^ 3 * u ^ 2 * v) * (1 - c ^ 3 * u * v ^ 2)) -
      (1 + c * u) * (1 + c * v) * (1 - c ^ 2 * u * v) =
      -(c ^ 4 * u * v * (u ^ 2 + u * v + v ^ 2)) +
        c ^ 6 * (u * v) ^ 3 * (1 + c * (u + v)) := by
  ring

/-- The remaining terms either couple a square part and a primitive part
or are at least quadratic in the primitive variables. -/
theorem gaussianMoebius_pair_content_correction (a c u v x y : ℂ) :
    let q (z : ℂ) := 1 - a * z + c * z ^ 2
    gaussianMoebiusPairContentFactor a c 0 u v x y -
        (1 + c * (u + v)) * q x * q y =
      -(c * (x ^ 2 + y ^ 2) + (q x - 1) * (q y - 1)) -
        c * (u + v) * (q x * q y - 1) := by
  dsimp only [gaussianMoebiusPairContentFactor]
  ring

/-- Joint contour positions and the two exponents after summing common
divisors through the surviving cutoff. -/
theorem gaussianMoebius_pair_content_exponents :
    let z : ℝ := 1251 / 10000
    let b : ℝ := 8734 / 10000
    let c := 1001 / 1000 * (b - z) + 2 * z
    1 / 4 < 2 * z ∧ 1 < 8 * z ∧ 1 < 2 * z + b ∧ 1 < 2 * b ∧
      archivedGaussianKnownBoundary < b ∧ 0 < b - z ∧
      z + b = 1997 / 2000 ∧ 2 / 7 + 3 / 14 * (z + b) = 13991 / 28000 ∧
      (13991 / 28000 : ℝ) < 1 / 2 ∧ c = 9992483 / 10000000 ∧ c < 1 ∧
      2 / 7 + 3 / 14 * c = 69977449 / 140000000 ∧ (69977449 / 140000000 : ℝ) < 1 / 2 := by
  norm_num [archivedGaussianKnownBoundary]

#print axioms gaussianMoebiusPairContent_diagonal
#print axioms archivedGaussianMoebius_pair_content
#print axioms archivedGaussianContentSign_cube
#print axioms gaussianMoebius_rational_square_correction
#print axioms gaussianMoebius_pair_content_correction
#print axioms gaussianMoebius_pair_content_exponents

end
end AlpogeSuperZeta
