import GaussianIndexWeights
import GaussianLowerPrimeWindow

/-! The centered window condition for the shifted common-divisor
indices gives the original lower prime window for the exact quartic. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Finset Set QuarticModel FieldTarget
open scoped Classical

noncomputable section

private def indexShiftCorrection : ℝ :=
  ∑' n : ℕ, archivedInertIndexWeight n 1 / (n : ℝ) / ((n + 1 : ℕ) : ℝ)

private def indexTailCorrection (f k : ℕ) : ℝ :=
  ∑' pj : Nat.Primes × ℕ, archivedInertIndexWeight pj.1.val f /
    (archivedInertTailIndex f k pj : ℝ)

private def indexTailRamp (f k : ℕ) (x : ℝ) : ℝ :=
  ∑' pj : Nat.Primes × ℕ, archivedInertIndexWeight pj.1.val f *
    indexRampWeight x (archivedInertTailIndex f k pj)

/-- Twice the inert-prime ramp in the exact shifted indices, minus the
base ramp and with the full adjustment of its linear term. -/
def archivedGaussianPrimitiveIndexRamp (x : ℝ) : ℝ :=
  2 * ((∑ n ∈ range (⌊x⌋₊ + 1), archivedInertIndexWeight n 1 * indexRampWeight x (n + 1)) +
    indexTailRamp 1 1 x + indexTailRamp 2 0 x) -
  (∑ n ∈ range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight x n) -
  ((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient) * x +
  2 * x * (indexShiftCorrection - indexTailCorrection 1 1 - indexTailCorrection 2 0)

private theorem indexUnshifted_eq (x : ℝ) :
    2 * (∑ n ∈ range (⌊x⌋₊ + 1), archivedInertIndexWeight n 1 * indexRampWeight x n) -
      (∑ n ∈ range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight x n) -
      ((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient) * x =
    -archivedGaussianPrimeOnlyRamp x := by
  let S := range (⌊x⌋₊ + 1)
  let a (n : ℕ) := vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0)
  have h :
      2 * (∑ n ∈ S, archivedInertIndexWeight n 1 * indexRampWeight x n) -
        (∑ n ∈ S, archivedIndexBaseWeight n * indexRampWeight x n) =
      -(∑ n ∈ S, a n * indexRampWeight x n) := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun n _ => ?_
    calc
      _ = (2 * archivedInertIndexWeight n 1 - archivedIndexBaseWeight n) * indexRampWeight x n := by
        ring
      _ = _ := by rw [archivedIndexWeight_balance, neg_mul]
  rw [h]
  simp only [archivedGaussianPrimeOnlyRamp, gaussianPrimeNormRamp, Deduction.ramp, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re, indexRampWeight, S, a]
  ring

/-- Shifting the degree-one indices and including the higher indices
preserves the original window exponent, including its strict threshold
at one half. -/
theorem archivedGaussianPrimitiveIndexRamp_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ ≤ 1) :
    ∃ D ≥ 0, ∀ x ≥ (1 : ℝ),
      |archivedGaussianPrimitiveIndexRamp x + archivedGaussianPrimeOnlyRamp x| ≤ D * x ^ θ := by
  let b (n : ℕ) := archivedInertIndexWeight n 1
  let A := ∑' n : ℕ, b n / (n : ℝ) ^ (1 + θ)
  let B := ∑' pj : Nat.Primes × ℕ, archivedInertIndexWeight pj.1.val 1 /
    (archivedInertTailIndex 1 1 pj : ℝ) ^ θ
  let C := ∑' pj : Nat.Primes × ℕ, archivedInertIndexWeight pj.1.val 2 /
    (archivedInertTailIndex 2 0 pj : ℝ) ^ θ
  have hA : 0 ≤ A := tsum_nonneg fun n =>
    div_nonneg (archivedInertIndexWeight_nonneg _ _) (Real.rpow_nonneg n.cast_nonneg _)
  have hB : 0 ≤ B := tsum_nonneg fun _ =>
    div_nonneg (archivedInertIndexWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC : 0 ≤ C := tsum_nonneg fun _ =>
    div_nonneg (archivedInertIndexWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨2 * (A + B + C), by positivity, fun x hx => ?_⟩
  have hxp := zero_lt_one.trans_le hx
  have hθ₀ : 0 ≤ θ := by linarith
  let S := range (⌊x⌋₊ + 1)
  let old := ∑ n ∈ S, b n * indexRampWeight x n
  let moved := ∑ n ∈ S, b n * indexRampWeight x (n + 1)
  let shiftLoss := x * indexShiftCorrection - (old - moved)
  let tailLoss (f k : ℕ) := x * indexTailCorrection f k - indexTailRamp f k x
  have he :
      archivedGaussianPrimitiveIndexRamp x + archivedGaussianPrimeOnlyRamp x =
        2 * shiftLoss - 2 * tailLoss 1 1 - 2 * tailLoss 2 0 := by
    rw [← neg_neg (archivedGaussianPrimeOnlyRamp x), ← indexUnshifted_eq]
    simp only [archivedGaussianPrimitiveIndexRamp, shiftLoss, tailLoss, old, moved, b, S]
    ring
  have hs' := centered_index_shift_bounds b (archivedInertIndexWeight_eq_zero_of_not_prime
    1 Nat.not_prime_zero) (fun n => archivedInertIndexWeight_nonneg n 1) hθ₀ hθ₁
    (archivedInertIndexWeight_one_summable (by linarith : 0 < θ)) hxp
  have hs : 0 ≤ shiftLoss ∧ shiftLoss ≤ x ^ θ * A := by
    simpa only [shiftLoss, old, moved, A, S, b, indexShiftCorrection, mul_sub,
      sum_sub_distrib] using hs'
  have h1 : 0 ≤ tailLoss 1 1 ∧ tailLoss 1 1 ≤ x ^ θ * B :=
    centered_index_ramp_bounds (fun pj : Nat.Primes × ℕ => archivedInertIndexWeight pj.1.val 1)
      (archivedInertTailIndex 1 1) (fun _ => archivedInertIndexWeight_nonneg _ _)
      (archivedInertTailIndex_pos 1 1) hθ₀ hθ₁ (archivedInertTail_summable 1 1 rfl hθ) hxp
  have h2 : 0 ≤ tailLoss 2 0 ∧ tailLoss 2 0 ≤ x ^ θ * C :=
    centered_index_ramp_bounds (fun pj : Nat.Primes × ℕ => archivedInertIndexWeight pj.1.val 2)
      (archivedInertTailIndex 2 0) (fun _ => archivedInertIndexWeight_nonneg _ _)
      (archivedInertTailIndex_pos 2 0) hθ₀ hθ₁ (archivedInertTail_summable 2 0 rfl hθ) hxp
  have hAX : 0 ≤ x ^ θ * A := by positivity
  have hBX : 0 ≤ x ^ θ * B := by positivity
  have hCX : 0 ≤ x ^ θ * C := by positivity
  rw [he, abs_le]
  exact ⟨by linarith only [hs.1, h1.2, h2.2, hAX],
    by linarith only [hs.2, h1.1, h2.1, hBX, hCX]⟩

def ArchivedGaussianPrimitiveIndexWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Icc Y (Y ^ (1 + δ)), archivedGaussianPrimitiveIndexRamp y ≤ C * y ^ θ

private theorem indexWindow_of_le_add {f g : ℝ → ℝ} {θ δ C D : ℝ}
    (h : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), g y ≤ C * y ^ θ)
    (hE : ∀ x ≥ (1 : ℝ), f x ≤ g x + D * x ^ θ) :
    ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), f y ≤ (C + D) * y ^ θ := by
  intro Y₀
  obtain ⟨Y, hY, hW⟩ := h (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have h1 := (le_max_right Y₀ (1 : ℝ)).trans (hY.trans hy.1)
  rw [add_mul]
  exact (hE y h1).trans (add_le_add (hW y hy) le_rfl)

theorem archivedGaussianPrimitiveIndexWindowBound_iff :
    ArchivedGaussianPrimitiveIndexWindowBound ↔ ArchivedGaussianPrimeOnlyLowerWindowBound := by
  constructor
  · intro h θ hθ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ hθ₁
    obtain ⟨D, hD, hE⟩ := archivedGaussianPrimitiveIndexRamp_error hθ hθ₁.le
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, indexWindow_of_le_add hW ?_⟩
    intro x hx
    linarith only [(abs_le.mp (hE x hx)).1]
  · intro h θ hθ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ hθ₁
    obtain ⟨D, hD, hE⟩ := archivedGaussianPrimitiveIndexRamp_error hθ hθ₁.le
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, indexWindow_of_le_add hW ?_⟩
    intro x hx
    linarith only [(abs_le.mp (hE x hx)).2]

theorem quartic_rh_of_primitive_index_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ArchivedGaussianPrimitiveIndexWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_lower_windows_and_real_positivity hD hpos
    (archivedGaussianPrimitiveIndexWindowBound_iff.mp hcut)

#print axioms archivedGaussianPrimitiveIndexRamp_error
#print axioms archivedGaussianPrimitiveIndexWindowBound_iff
#print ArchivedGaussianPrimitiveIndexWindowBound
#check quartic_rh_of_primitive_index_windows
#print axioms quartic_rh_of_primitive_index_windows

end
end AlpogeSuperZeta
