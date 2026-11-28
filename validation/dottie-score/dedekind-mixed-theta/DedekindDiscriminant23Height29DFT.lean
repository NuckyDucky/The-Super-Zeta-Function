import Height29DFTSum.Block00
import Height29DFTSum.Block01
import Height29DFTSum.Block02
import Height29DFTSum.Block03
import Height29DFTSum.Block04
import Height29DFTSum.Block05
import Height29DFTSum.Block06
import Height29DFTSum.Block07
import Height29DFTSum.Block08
import Height29DFTSum.Block09
import Height29DFTSum.Block10
import Height29DFTSum.Block11
import Height29DFTSum.Block12
import Height29DFTSum.Block13
import Height29DFTSum.Block14
import Height29DFTSum.Block15
import Height29DFTSum.Block16
import Height29DFTSum.Block17
import Height29DFTSum.Block18
import Height29DFTSum.Block19
import Height29DFTSum.Block20
import Height29DFTSum.Block21
import Height29DFTSum.Block22
import DedekindDiscriminant23Height29CircleCertificate

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

noncomputable section

local notation "L23" => Discriminant23GaloisField
local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "T29" => (29 + 1 / 512 : ℝ)
local notation "c29" => dottieScaledRightCenter T29 0
local notation "ρ29" => dottieWeightOuterRadius 0
local notation "F29" => (fun w : ℂ ↦ 8 * discriminant23CompletedClassProduct w)

set_option exponentiation.threshold 512

private def height29ModelNumerator (k : ℕ) : GaussianInt :=
  let a := discriminant23ModelNumerators[k]!
  ⟨a.1, a.2⟩

private theorem height29_scaled_model_coeff {k : ℕ} (hk : k < 113) :
    discriminant23Height29ScaledModelCoeff k =
      gaussianScaled (height29ModelNumerator k) (height29SampleDenominator * 2 ^ k) := by
  rw [discriminant23Height29ScaledModelCoeff, dite_eq_left hk]
  simp only [discriminant23Height29Model, height29ModelNumerator, gaussianScaled,
    GaussianInt.toComplex_def, height29SampleDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  rw [div_pow, one_pow]
  ring

private def height29DFTResidualNumerator (k : ℕ) : GaussianInt :=
  ((2 ^ k : ℕ) : GaussianInt) *
      gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 k 128 -
    ((128 * contourRoot128Scale : ℕ) : GaussianInt) * height29ModelNumerator k

private def height29DFTResidualDenominator (k : ℕ) : ℕ :=
  128 * height29SampleDenominator * contourRoot128Scale * 2 ^ k

private abbrev height29RoundingCheck (k : ℕ) : Prop :=
  gaussianNormCeiling (height29DFTResidualNumerator k) * 10 ^ 73 ≤
    height29DFTResidualDenominator k * 1

private theorem height29_check_of_dft_sum {k : ℕ} (a : GaussianInt)
    (hSum : gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 k 128 = a)
    (hBound : gaussianNormCeiling
        (((2 ^ k : ℕ) : GaussianInt) * a -
          ((128 * contourRoot128Scale : ℕ) : GaussianInt) * height29ModelNumerator k) *
        10 ^ 73 ≤ height29DFTResidualDenominator k * 1) :
    height29RoundingCheck k := by
  unfold height29RoundingCheck height29DFTResidualNumerator
  rwa [hSum]

private theorem height29_dft_sum_first (a : Fin 22) (b : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (a.val * 5 + b.val) 128 =
      height29DFTSumWitness (a.val * 5 + b.val) := by
  fin_cases a
  · exact height29_dft_sum_block_00 b
  · exact height29_dft_sum_block_01 b
  · exact height29_dft_sum_block_02 b
  · exact height29_dft_sum_block_03 b
  · exact height29_dft_sum_block_04 b
  · exact height29_dft_sum_block_05 b
  · exact height29_dft_sum_block_06 b
  · exact height29_dft_sum_block_07 b
  · exact height29_dft_sum_block_08 b
  · exact height29_dft_sum_block_09 b
  · exact height29_dft_sum_block_10 b
  · exact height29_dft_sum_block_11 b
  · exact height29_dft_sum_block_12 b
  · exact height29_dft_sum_block_13 b
  · exact height29_dft_sum_block_14 b
  · exact height29_dft_sum_block_15 b
  · exact height29_dft_sum_block_16 b
  · exact height29_dft_sum_block_17 b
  · exact height29_dft_sum_block_18 b
  · exact height29_dft_sum_block_19 b
  · exact height29_dft_sum_block_20 b
  · exact height29_dft_sum_block_21 b

private theorem height29_dft_sum_checked {k : ℕ} (hk : k < 113) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 k 128 =
      height29DFTSumWitness k := by
  by_cases hFirst : k < 110
  · let a : Fin 22 := ⟨k / 5, by omega⟩
    let b : Fin 5 := ⟨k % 5, by omega⟩
    have hEq : a.val * 5 + b.val = k := by dsimp [a, b]; omega
    simpa only [hEq] using height29_dft_sum_first a b
  · let b : Fin 3 := ⟨k - 110, by omega⟩
    have hEq : 110 + b.val = k := by dsimp [b]; omega
    simpa only [hEq] using height29_dft_sum_block_22 b

set_option maxHeartbeats 5000000 in
private theorem height29_dot_bounds_checked :
    ∀ k : Fin 113, gaussianNormCeiling
        (((2 ^ k.val : ℕ) : GaussianInt) * height29DFTSumWitness k -
          ((128 * contourRoot128Scale : ℕ) : GaussianInt) * height29ModelNumerator k) *
        10 ^ 73 ≤ height29DFTResidualDenominator k * 1 := by
  decide +kernel

private theorem height29_rounding_checked {k : ℕ} (hk : k < 113) : height29RoundingCheck k :=
  height29_check_of_dft_sum _ (height29_dft_sum_checked hk) (height29_dot_bounds_checked ⟨k, hk⟩)

private theorem height29_rational_dft_error {k : ℕ} (hk : k < 113) :
    ‖gaussianDFTCoeff height29SampleNumerator contourRoot128PhaseNumerator 128 k
        height29SampleDenominator contourRoot128Scale -
      discriminant23Height29ScaledModelCoeff k‖ ≤ 1 / 10 ^ 73 := by
  rw [height29_scaled_model_coeff hk, gaussianDFTCoeff_sub_scaled _ _
    (by norm_num) (by norm_num [height29SampleDenominator])
    (by norm_num [contourRoot128Scale]) (by positivity)]
  have hDenom : 0 < height29DFTResidualDenominator k := by
    unfold height29DFTResidualDenominator height29SampleDenominator contourRoot128Scale
    positivity
  change ‖gaussianScaled (height29DFTResidualNumerator k) (height29DFTResidualDenominator k)‖ ≤ _
  calc
    _ ≤ ((1 : ℕ) : ℝ) / ((10 ^ 73 : ℕ) : ℝ) :=
      norm_gaussianScaled_le_of_nat_bound (p := 1) (q := 10 ^ 73)
        hDenom (by norm_num) (height29_rounding_checked hk)
    _ = _ := by rw [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- The root enclosure and integer dot products certify all the rounded coefficients. -/
theorem discriminant23_height29_samples_rounding (k : ℕ) (hk : k < 113) :
    ‖contourSampleCoeff discriminant23Height29Samples discriminant23Height29Root 128 k -
        discriminant23Height29ScaledModelCoeff k‖ ≤ 1 / 10 ^ 72 := by
  let A := gaussianDFTCoeff height29SampleNumerator contourRoot128PhaseNumerator 128 k
    height29SampleDenominator contourRoot128Scale
  have hPhaseError : ‖contourSampleCoeff discriminant23Height29Samples discriminant23Height29Root 128 k -
      A‖ ≤ (1 / 10 ^ 53 : ℝ) * (1 / 10 ^ 24) := by
    change ‖contourSampleCoeff discriminant23Height29Samples contourRoot128 128 k -
      A‖ ≤ (1 / 10 ^ 53 : ℝ) * (1 / 10 ^ 24)
    exact norm_contourSampleCoeff_sub_gaussianDFT_le
      (ω := contourRoot128) (N := 128) (k := k) (s := height29SampleNumerator)
      (phases := contourRoot128PhaseNumerator) (ds := height29SampleDenominator)
      (dp := contourRoot128Scale) (C := 1 / 10 ^ 53) (δ := 1 / 10 ^ 24) (by norm_num)
      contourRoot128_isPrimitive.pow_eq_one height29_sample_size contourRoot128_phase_error
  calc
    _ ≤ ‖contourSampleCoeff discriminant23Height29Samples discriminant23Height29Root 128 k - A‖ +
        ‖A - discriminant23Height29ScaledModelCoeff k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 / 10 ^ 53 : ℝ) * (1 / 10 ^ 24) + 1 / 10 ^ 73 :=
      add_le_add hPhaseError (height29_rational_dft_error hk)
    _ ≤ _ := by norm_num

/-- For this fixed dyadic sample table, only the actual reading enclosures remain as input. -/
theorem discriminant23_height29_ne_zero_of_sample_enclosures
    (hSample : ∀ j < 128, ‖discriminant23Height29Samples j -
      F29 (c29 + ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j)‖ ≤ 1 / 10 ^ 60)
    {w : ℂ} (hw : w ∈ closedBall c29 ρ29) :
    mixedThetaContinuation L23 w ≠ 0 ∧
      mixedThetaContinuation F23 w ≠ 0 ∧ discriminant23CharacterFold w ≠ 0 :=
  discriminant23_height29_ne_zero_of_coarser_sample_enclosures discriminant23Height29Samples
    hSample discriminant23_height29_samples_rounding hw

#check @discriminant23_height29_ne_zero_of_sample_enclosures
#print axioms discriminant23_height29_samples_rounding
#print axioms discriminant23_height29_ne_zero_of_sample_enclosures

end
end FieldTarget
