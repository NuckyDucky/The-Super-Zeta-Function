import GaussianBalancedMoebius
import GaussianMoebiusContent
import GaussianPrimeSupport
import Mathlib.Algebra.Polynomial.Roots

/-! Separate the common divisor of the two Gaussian Möbius inputs. The
signed local factors and the diagonal squared coefficients are both exact. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Finset QuarticModel PowerSeries
open scoped Classical

noncomputable section

private theorem archivedMoebiusPolynomial (p : ℕ) [Fact p.Prime] :
    (∏ I : ↥(gaussianPrimesAbove p), (1 -
      Polynomial.C (archivedIdealCharacter I.val : ℂ) * Polynomial.X ^ I.val.inertiaDeg ℤ)) =
      (1 - Polynomial.C (archivedGaussianPrimeWeight p : ℂ) * Polynomial.X +
        Polynomial.C (archivedGaussianContentSign p : ℂ) * Polynomial.X ^ 2) := by
  apply Polynomial.funext
  intro v
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_add]
  have h := archivedGaussianContentEulerFactor_diagonal p v
  rw [← Finset.prod_coe_sort (gaussianPrimesAbove p)
    (fun I => (1 : ℂ) - (archivedIdealCharacter I : ℂ) * v ^ I.inertiaDeg ℤ)] at h
  rw [← h]
  unfold archivedGaussianContentEulerFactor
  ring

/-- The exact reciprocal Euler polynomial in the rational norm variable. -/
theorem archivedGaussianMoebius_ratio_prime_power {p : ℕ} (hp : p.Prime) (j : ℕ) :
    archivedGaussianMoebiusCoefficients (p ^ j) =
      if j = 0 then 1 else if j = 1 then -(archivedGaussianPrimeWeight p : ℂ)
        else if j = 2 then (archivedGaussianContentSign p : ℂ) else 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [archivedGaussianMoebius_prime_power hp]
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
    (archivedMoebiusPolynomial p)
  simp only [map_prod, map_sub, map_one, map_mul, map_pow, map_add,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] at h
  rw [h]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  split_ifs <;> simp_all

/-- The local pair with fixed common-divisor exponent j. The remaining two
variables represent coprime parts. -/
def gaussianMoebiusPairFactor (a c : ℂ) (j : ℕ) (u v : ℂ) : ℂ :=
  match j with
  | 0 => 1 - a * (u + v) + c * (u ^ 2 + v ^ 2)
  | 1 => a ^ 2 - a * c * (u + v)
  | 2 => c ^ 2
  | _ + 3 => 0

theorem archivedGaussianMoebius_pair_factor {p : ℕ} (hp : p.Prime) (j : ℕ) (u v : ℂ) :
    let A := archivedGaussianMoebiusCoefficients
    A (p ^ j) ^ 2 + A (p ^ j) * A (p ^ (j + 1)) * (u + v) +
      A (p ^ j) * A (p ^ (j + 2)) * (u ^ 2 + v ^ 2) =
      gaussianMoebiusPairFactor (archivedGaussianPrimeWeight p : ℂ)
        (archivedGaussianContentSign p : ℂ) j u v := by
  dsimp only
  simp only [archivedGaussianMoebius_ratio_prime_power hp]
  rcases j with _ | _ | _ | j
  · simp [gaussianMoebiusPairFactor, sub_eq_add_neg]
  · simp [gaussianMoebiusPairFactor, sub_eq_add_neg, neg_mul]
  · simp [gaussianMoebiusPairFactor]
  · simp [gaussianMoebiusPairFactor, show j + 3 ≠ 2 by omega,
      show j + 3 + 1 ≠ 2 by omega]

/-- Forgetting the common-divisor label puts x at u*v and recovers exactly
the product of the two original local inverse factors. -/
theorem gaussianMoebiusPairFactor_forget (a c u v x : ℂ) :
    gaussianMoebiusPairFactor a c 0 u v + x * gaussianMoebiusPairFactor a c 1 u v +
        x ^ 2 * gaussianMoebiusPairFactor a c 2 u v -
        (1 - a * u + c * u ^ 2) * (1 - a * v + c * v ^ 2) =
      (x - u * v) * (a ^ 2 - a * c * (u + v) + c ^ 2 * (x + u * v)) := by
  unfold gaussianMoebiusPairFactor
  ring

/-- The Euler factor of the sum of squares of the signed coefficients. -/
def archivedGaussianMoebiusSecondFactor (p : ℕ) (x : ℂ) : ℂ :=
  1 + archivedGaussianMoebiusCoefficients p ^ 2 * x +
    archivedGaussianMoebiusCoefficients (p ^ 2) ^ 2 * x ^ 2

private theorem prime_char_cases {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    (ZMod.χ₄ (p : ZMod 4) = 1 ∨ ZMod.χ₄ (p : ZMod 4) = -1) ∧
      (rationalNormSign p = 1 ∨ rationalNormSign p = -1) := by
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  constructor
  · by_cases h : p % 4 = 1
    · exact Or.inl (ZMod.χ₄_nat_one_mod_four h)
    · exact Or.inr (ZMod.χ₄_nat_three_mod_four (by omega))
  · rw [← rationalNormSign_reciprocity p hp]
    apply legendreSym.eq_one_or_neg_one
    simpa only [Int.cast_ofNat] using norm_discriminant_ne_zero hc

private theorem archivedGaussianMoebiusSecondFactor_good {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hc : p.Coprime 26509772707289) (x : ℂ) :
    archivedGaussianMoebiusSecondFactor p x =
      1 + (1 + (ZMod.χ₄ (p : ZMod 4) : ℂ)) * (1 + (rationalNormSign p : ℂ)) * x + x ^ 2 := by
  have hp' : p.Prime := Fact.out
  have h₁ := archivedGaussianMoebius_ratio_prime_power hp' 1
  simp only [pow_one, one_ne_zero, if_false, if_true] at h₁
  have h₂ := archivedGaussianMoebius_ratio_prime_power hp' 2
  norm_num at h₂
  have hsq : (archivedGaussianPrimeWeight p : ℂ) ^ 2 =
      (1 + (ZMod.χ₄ (p : ZMod 4) : ℂ)) * (1 + (rationalNormSign p : ℂ)) := by
    exact_mod_cast archivedGaussianPrimeWeight_sq hp hc
  have hcontent : (archivedGaussianContentSign p : ℂ) ^ 2 = 1 := by
    rcases prime_char_cases hp hc with ⟨ha | ha, hb | hb⟩ <;>
      norm_num [archivedGaussianContentSign, ha, hb]
  rw [archivedGaussianMoebiusSecondFactor, h₁, h₂, neg_sq, hsq, hcontent, one_mul]

/-- The two possible Euler corrections after extracting the four rational
Dirichlet characters. The next coefficients are those at powers 2 and 3. -/
theorem archivedGaussianMoebiusSecondFactor_correction {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hc : p.Coprime 26509772707289) (x : ℂ) :
    let b : ℂ := ZMod.χ₄ (p : ZMod 4)
    let e : ℂ := rationalNormSign p
    let q := (1 + b) * (1 + e)
    archivedGaussianMoebiusSecondFactor p x * ((1 - x) * (1 - b * x) *
        (1 - e * x) * (1 - b * e * x)) =
      1 - (1 + 2 * q) * x ^ 2 + 4 * q * x ^ 3 - (1 + 2 * q) * x ^ 4 + x ^ 6 := by
  dsimp only
  rw [archivedGaussianMoebiusSecondFactor_good hp hc]
  rcases prime_char_cases hp hc with ⟨ha | ha, hb | hb⟩ <;>
    norm_num [ha, hb] <;> ring

private theorem archivedGaussianMoebiusSecondFactor_five (x : ℂ) :
    archivedGaussianMoebiusSecondFactor 5 x = 1 + 4 * x + x ^ 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : Nat.Coprime 5 26509772707289 := by decide +kernel
  have hs := (archivedGaussianPrimeWeight_ne_zero_iff (p := 5) (by decide) hc).mp
    (by rw [archivedGaussianPrimeWeight_at_5_and_13.1]; norm_num)
  rw [archivedGaussianMoebiusSecondFactor_good (p := 5) (by decide) hc,
    ZMod.χ₄_nat_one_mod_four hs.1, hs.2]
  norm_num

/-- The small negative root at the first active split prime. Its modulus
is the earlier reciprocal radius 2 minus the square root of 3. -/
theorem archivedGaussianMoebiusSecondFactor_radius :
    archivedGaussianMoebiusSecondFactor 5 ((√(3 : ℝ) : ℂ) - 2) = 0 := by
  rw [archivedGaussianMoebiusSecondFactor_five]
  have h : (((√(3 : ℝ) : ℝ) : ℂ)) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination h

/-- Fixed contour and common-divisor cutoff used in the quantitative bound. -/
theorem gaussianMoebius_commonDivisor_exponent :
    let b : ℝ := 8734 / 10000
    archivedGaussianKnownBoundary < b ∧ 1 / 2 < b ∧
      b + (1 - 2 * b) / 4 = 6867 / 10000 ∧
      (6867 / 10000 : ℝ) < archivedGaussianKnownBoundary := by
  norm_num [archivedGaussianKnownBoundary]

/-- A difference between two neighboring scales. Its zeros have real
part equal to the exponent used to weight the smaller scale. -/
def gaussianScaleDifference (a : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.exp (((a : ℂ) - z) * (Real.log 2 : ℂ))

/-- Remove the residues at the two real exponents of the squared weights. -/
def gaussianPairDiagonalFilter (z : ℂ) : ℂ :=
  gaussianScaleDifference (1 / 2) z * gaussianScaleDifference (1 / 6) z ^ 4

theorem gaussianPairDiagonalFilter_zeros :
    gaussianPairDiagonalFilter ((1 / 2 : ℝ) : ℂ) = 0 ∧
      gaussianPairDiagonalFilter ((1 / 6 : ℝ) : ℂ) = 0 := by
  constructor <;> simp [gaussianPairDiagonalFilter, gaussianScaleDifference]

theorem gaussianPairDiagonalFilter_ne_zero {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    gaussianPairDiagonalFilter z ≠ 0 := by
  have hn (a : ℝ) (ha : a < z.re) : gaussianScaleDifference a z ≠ 0 := by
    intro h
    have heq : (1 : ℂ) = Complex.exp (((a : ℂ) - z) * (Real.log 2 : ℂ)) := sub_eq_zero.mp h
    have hnorm := congrArg (fun w : ℂ => ‖w‖) heq
    rw [norm_one, Complex.norm_exp] at hnorm
    have he : (((a : ℂ) - z) * (Real.log 2 : ℂ)).re < 0 := by
      simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr ha) (Real.log_pos (by norm_num))
    exact (Real.exp_lt_one_iff.mpr he).ne hnorm.symm
  unfold gaussianPairDiagonalFilter
  exact mul_ne_zero (hn _ hz) (pow_ne_zero _ (hn _ (by linarith)))

/-- Finite inverse of the scale difference with an explicit endpoint term. -/
theorem gaussianScaleDifference_telescope (f : ℝ → ℂ) (a : ℂ) (y : ℝ) (n : ℕ) :
    (∑ j ∈ range n, a ^ j * (f (y / (2 : ℝ) ^ j) - a * f (y / (2 : ℝ) ^ (j + 1)))) =
      f y - a ^ n * f (y / (2 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ a n]
    ring

theorem gaussianMoebius_smallRay_exponent :
    (1 / 4 : ℝ) / 2 = 1 / 8 ∧ 1 / 8 + (3 / 14) * (2 - 1 / 4) = 1 / 2 := by
  norm_num

#print axioms archivedGaussianMoebius_ratio_prime_power
#print axioms archivedGaussianMoebius_pair_factor
#print axioms gaussianMoebiusPairFactor_forget
#print axioms archivedGaussianMoebiusSecondFactor_correction
#print axioms archivedGaussianMoebiusSecondFactor_radius
#print axioms gaussianMoebius_commonDivisor_exponent
#print axioms gaussianPairDiagonalFilter_zeros
#print axioms gaussianPairDiagonalFilter_ne_zero
#print axioms gaussianScaleDifference_telescope
#print axioms gaussianMoebius_smallRay_exponent

end
end AlpogeSuperZeta
