import GaussianSeventhFreeMellin
import ArchivedGaussianLogDerivative
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The two-factor Möbius cutoff and the reflected Mellin weight for the
actual archived Gaussian coefficient sequence. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Finset PowerSeries QuarticModel
open FieldCoefficientTransfer ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

private abbrev signedCoefficientOne : Invertible (signedIdealCoefficients 1) :=
  invertibleOfNonzero (by rw [signedIdealCoefficients_multiplicative.map_one]; exact one_ne_zero)

/-- The norm coefficients of the reciprocal Gaussian series. -/
def archivedGaussianMoebiusCoefficients : ArithmeticFunction ℂ :=
  dirichletInverse signedIdealCoefficients signedCoefficientOne

theorem archivedGaussianMoebius_mul_signed : archivedGaussianMoebiusCoefficients *
    signedIdealCoefficients = 1 :=
  dirichletInverse_mul_self signedIdealCoefficients signedCoefficientOne

private def powerValues (p : ℕ) (f : ArithmeticFunction ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => f (p ^ j))

private theorem powerValues_mul {p : ℕ} (hp : p.Prime) (f g : ArithmeticFunction ℂ) :
    powerValues p (f * g) = powerValues p f * powerValues p g := by
  ext j
  rw [powerValues, coeff_mk, ← ofPowerSeries_apply_pow hp.one_lt, map_mul,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hd₁ := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hpair)
  have hd₂ := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hpair)
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd₁
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd₂
  rw [hi, hk, ofPowerSeries_apply_pow hp.one_lt, ofPowerSeries_apply_pow hp.one_lt]
  simp only [powerValues, coeff_mk]

/-- The inverse coefficients come from taking each actual Gaussian prime
ideal at most once, with its sign and its own inertia degree. -/
theorem archivedGaussianMoebius_prime_power {p : ℕ} (hp : p.Prime) (j : ℕ) :
    archivedGaussianMoebiusCoefficients (p ^ j) =
      coeff j (∏ I : ↥(gaussianPrimesAbove p),
        (1 - C (archivedIdealCharacter I.val : ℂ) * (X : PowerSeries ℂ) ^ I.val.inertiaDeg ℤ)) := by
  let : Fact p.Prime := ⟨hp⟩
  let Q : PowerSeries ℂ := ∏ I : ↥(gaussianPrimesAbove p),
    (1 - C (archivedIdealCharacter I.val : ℂ) * X ^ I.val.inertiaDeg ℤ)
  have hB : powerValues p signedIdealCoefficients = signedLocalEulerSeries p := by
    ext i
    rw [powerValues, coeff_mk, ← signedIdealNormSum_primePower p i]
    simp only [signedIdealCoefficients, toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (pow_ne_zero _ hp.ne_zero)]
  have hQ : signedLocalEulerSeries p * Q = 1 := by
    unfold signedLocalEulerSeries Q
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro I _
    exact weightedGeometricAtDegree_mul_denominator _
      (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt I).ne'
  have hUnit : powerValues p (1 : ArithmeticFunction ℂ) = 1 := by
    ext i
    rw [powerValues, coeff_mk, coeff_one, ArithmeticFunction.one_apply]
    by_cases h : i = 0
    · simp [h]
    · have hpw : p ^ i ≠ 1 := ne_of_gt (one_lt_pow' hp.one_lt h)
      rw [if_neg hpw, if_neg h]
  have hA : powerValues p archivedGaussianMoebiusCoefficients * signedLocalEulerSeries p = 1 := by
    rw [← hB, ← powerValues_mul hp, archivedGaussianMoebius_mul_signed, hUnit]
  have heq : powerValues p archivedGaussianMoebiusCoefficients = Q := by
    calc
      _ = powerValues p archivedGaussianMoebiusCoefficients * (signedLocalEulerSeries p * Q) := by
        rw [hQ, mul_one]
      _ = Q := by rw [← mul_assoc, hA, one_mul]
  simpa only [powerValues, coeff_mk] using congrArg (coeff j) heq

/-- Keep the coefficients up to and including a norm cutoff. -/
def normCutoff (u : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ u then f n else 0, by simp⟩

/-- The exact two-factor decomposition, including the convolution remainder. -/
theorem archivedGaussianMoebius_square_identity (u : ℕ) :
    let A := archivedGaussianMoebiusCoefficients
    let B := signedIdealCoefficients
    let P := normCutoff u A
    (A - P)^2 * B = A - (P + P) + P^2 * B := by
  dsimp only
  let A := archivedGaussianMoebiusCoefficients
  let B := signedIdealCoefficients
  let P := normCutoff u A
  calc
    _ = A * (A * B) - (P + P) * (A * B) + P^2 * B := by ring
    _ = _ := by rw [show A * B = 1 from archivedGaussianMoebius_mul_signed, mul_one, mul_one]

private theorem above_square_eq_zero (A : ArithmeticFunction ℂ) (u n : ℕ)
    (hn : n ≤ u^2) : ((A - normCutoff u A)^2) n = 0 := by
  rw [pow_two, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro pair hpair
  have hp : pair.1 * pair.2 = n := (Nat.mem_divisorsAntidiagonal.mp hpair).1
  have hcut : pair.1 ≤ u ∨ pair.2 ≤ u := by
    by_contra! h
    exact (Nat.not_lt_of_ge hn) (by rw [← hp, pow_two]; exact Nat.mul_lt_mul_of_lt_of_lt h.1 h.2)
  have hzero (k : ℕ) (hk : k ≤ u) : (A - normCutoff u A) k = 0 := by
    rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
    change A k + -(if k ≤ u then A k else 0) = 0
    rw [if_pos hk, add_neg_cancel]
  rcases hcut with h | h
  · rw [hzero _ h, zero_mul]
  · rw [hzero _ h, mul_zero]

private theorem above_square_mul_eq_zero (A B : ArithmeticFunction ℂ) (u n : ℕ)
    (hn : n ≤ u^2) : ((A - normCutoff u A)^2 * B) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro pair hpair
  have hle := (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hpair)).trans hn
  rw [above_square_eq_zero A u _ hle, zero_mul]

/-- Through the square of the cutoff the actual coefficients need only
Möbius inputs up to the cutoff, with one full signed Gaussian convolution. -/
theorem archivedGaussianMoebius_square_cutoff {u n : ℕ} (hn : n ≤ u^2) :
    let A := archivedGaussianMoebiusCoefficients
    let P := normCutoff u A
    A n = 2 * P n - (P^2 * signedIdealCoefficients) n := by
  dsimp only
  let A := archivedGaussianMoebiusCoefficients
  let P := normCutoff u A
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (archivedGaussianMoebius_square_identity u)
  change ((A - P)^2 * signedIdealCoefficients) n =
    (A - (P + P) + P^2 * signedIdealCoefficients) n at h
  rw [above_square_mul_eq_zero A signedIdealCoefficients u n hn] at h
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply] at h
  linear_combination -h

/-- Mellin reading after the unrestricted signed Gaussian sum is folded
into the original theta weight. -/
def archivedGaussianBalancedMellin (z : ℂ) : ℂ :=
  archivedMellin (z / 7) * archivedGaussianFactor z / 7

theorem archivedGaussianBalancedMellin_entire :
    Differentiable ℂ archivedGaussianBalancedMellin := by
  exact (((archivedMellin_differentiable archivedTheta_reflection).comp
    (differentiable_id.div_const (7 : ℂ))).mul archivedGaussianFactor_entire).div_const 7

/-- Reflection of both Mellin arguments into the convergent half-plane.
The Gamma factors on this side control the lower tail of the kernel. -/
theorem archivedGaussianBalancedMellin_reflect {z : ℂ} (hz : z.re < 0) :
    archivedGaussianBalancedMellin z =
      archivedMellin (1 - z / 7) * archivedGaussianFactor (1 - z) *
        (archivedThetaScale : ℂ) ^ (1 - 2 * z) *
        Gamma (1 - z) ^ 2 * sin ((Real.pi : ℂ) * z) / (7 * (Real.pi : ℂ)) := by
  let c : ℂ := archivedThetaScale
  let πc : ℂ := Real.pi
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hπ : πc ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ₁ : Gamma (1 - z) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [sub_re, one_re]; linarith)
  have hc₁ : c ^ (1 - z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc)
  have hF : archivedMellin (1 - z) =
      archivedGaussianFactor (1 - z) * (c ^ (1 - z)) * Gamma (1 - z) := by
    unfold archivedGaussianFactor
    change _ = archivedMellin (1 - z) * (c ^ (1 - z))⁻¹ * (Gamma (1 - z))⁻¹ *
      c ^ (1 - z) * Gamma (1 - z)
    field_simp
  have hE : Gamma z * Gamma (1 - z) = πc / sin (πc * z) :=
    Gamma_mul_Gamma_one_sub z
  have hInv : (Gamma z)⁻¹ = Gamma (1 - z) * sin (πc * z) / πc := by
    by_cases hs : sin (πc * z) = 0
    · rw [hs, div_zero] at hE
      simp [(mul_eq_zero.mp hE).resolve_right hΓ₁, hs]
    · have hzΓ : Gamma z ≠ 0 := by
        intro hzero
        exact (div_ne_zero hπ hs) (by simpa only [hzero, zero_mul] using hE.symm)
      have h := (div_eq_iff hs).mp hE.symm
      apply (eq_div_iff hπ).mpr
      calc
        (Gamma z)⁻¹ * πc = (Gamma z)⁻¹ * ((Gamma z * Gamma (1 - z)) * sin (πc * z)) := by
          exact congrArg (fun a : ℂ => (Gamma z)⁻¹ * a) h
        _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hzΓ, one_mul]
  have hPow : (c ^ (1 - z)) * (c ^ z)⁻¹ = c ^ (1 - 2 * z) := by
    rw [← cpow_neg, ← cpow_add _ _ hc]
    congr 1
    ring
  unfold archivedGaussianBalancedMellin
  nth_rw 1 [← archivedMellin_functional_equation (z / 7)]
  conv_lhs =>
    rw [archivedGaussianFactor, ← archivedMellin_functional_equation z, hF]
  change archivedMellin (1 - z / 7) *
    (archivedGaussianFactor (1 - z) * c ^ (1 - z) * Gamma (1 - z) *
      (c ^ z)⁻¹ * (Gamma z)⁻¹) / 7 = _
  rw [hInv]
  calc
    _ = archivedMellin (1 - z / 7) * archivedGaussianFactor (1 - z) *
        (c ^ (1 - z) * (c ^ z)⁻¹) *
        Gamma (1 - z) ^ 2 * sin (πc * z) / (7 * πc) := by ring
    _ = _ := by rw [hPow]

/-- The logarithmic width follows from the sum of the three reflected
Gamma orders and the square-root cutoff. -/
theorem archivedGaussianBalanced_exponents :
    (1 / 7 : ℝ) + 2 = 15 / 7 ∧
    (15 / 7 : ℝ) * (12 / 25) - 1 = 1 / 35 ∧
    (15 / 7 : ℝ) + 1 / 14 = 31 / 14 := by
  norm_num

#print axioms archivedGaussianMoebius_mul_signed
#print axioms archivedGaussianMoebius_prime_power
#print axioms archivedGaussianMoebius_square_identity
#print axioms archivedGaussianMoebius_square_cutoff
#print axioms archivedGaussianBalancedMellin_entire
#print axioms archivedGaussianBalancedMellin_reflect
#print axioms archivedGaussianBalanced_exponents

end
end AlpogeSuperZeta
