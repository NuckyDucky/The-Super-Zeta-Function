import DedekindDiscriminant23Height29FourierError
import DedekindDiscriminant23Height29ExactBounds
import DedekindWideOuterDottie

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

noncomputable section

local notation "L23" => Discriminant23GaloisField
local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "T29" => (29 + 1 / 512 : ℝ)
local notation "c29" => dottieScaledRightCenter T29 0
local notation "ρ29" => dottieWeightOuterRadius 0
local notation "F29" => (fun w : ℂ ↦ 8 * discriminant23CompletedClassProduct w)

set_option exponentiation.threshold 512

def discriminant23Height29Root : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I / 128)

theorem discriminant23_height29_root_primitive :
    IsPrimitiveRoot discriminant23Height29Root 128 :=
  Complex.isPrimitiveRoot_exp 128 (by norm_num)

theorem discriminant23_height29_model_holomorphic :
    DifferentiableOn ℂ F29 (closedBall c29 2) := by
  have hPole := dottie_outerDisk_avoids_poles (T := T29) (ρ := 2) 0 (by norm_num)
  refine ((mixedThetaOuterReading_differentiableOn L23).mono hPole).congr ?_
  intro z hz
  obtain ⟨h₀, h₁⟩ := hPole hz
  exact (discriminant23_completedFold_eq_classProduct_off_poles z h₀ h₁).symm

theorem discriminant23_height29_cauchy_bound {w : ℂ} (hw : w ∈ closedBall c29 2) :
    ‖F29 w‖ ≤ 2 ^ 12 := by
  have hDist : ‖w - c29‖ ≤ (2 : ℝ) := (dist_eq_norm w c29) ▸ mem_closedBall.mp hw
  have hReal := abs_le.mp ((abs_re_le_norm (w - c29)).trans hDist)
  have hImag := abs_le.mp ((abs_im_le_norm (w - c29)).trans hDist)
  have hCenterRe : Complex.re c29 = 3 / 4 := by
    rw [discriminant23_height29_dottie_geometry.1]
    norm_num [Complex.mul_re]
  have hCenterIm : Complex.im c29 = 29 := by
    rw [discriminant23_height29_dottie_geometry.1]
    norm_num [Complex.mul_im]
  rw [sub_re, hCenterRe] at hReal
  rw [sub_im, hCenterIm] at hImag
  exact discriminant23_completedClassProduct_norm_le_on_upper_strip
    (by linarith only [hReal.1]) (by linarith only [hReal.2]) (by linarith only [hImag.1])

/-- Finite sample and rounding enclosures give the exact circle error budget. -/
theorem discriminant23_height29_model_error_le_finite_budget
    (samples : ℕ → ℂ)
    {sampleError roundingError : ℝ}
    (hSample : ∀ j < 128, ‖samples j -
      F29 (c29 + ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j)‖ ≤ sampleError)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples discriminant23Height29Root 128 k -
      discriminant23Height29ScaledModelCoeff k‖ ≤ roundingError)
    (w : ℂ) (hw : w ∈ closedBall c29 ρ29) :
    ‖F29 w - dottieRationalWeight c29 discriminant23Height29Model w‖ ≤
      discriminant23Height29CircleErrorBudget sampleError roundingError :=
  discriminant23_height29_model_error_le_circle_budget samples
    discriminant23_height29_root_primitive
    (discriminant23_height29_root_primitive.norm'_eq_one (by norm_num))
    discriminant23_height29_model_holomorphic
    (fun _ hz ↦ (discriminant23_height29_cauchy_bound (sphere_subset_closedBall hz)).trans (by norm_num))
    hSample hRound w hw

/-- The two finite error tables provide the uniform model error. -/
theorem discriminant23_height29_model_error_of_finite_enclosures
    (samples : ℕ → ℂ)
    (hSample : ∀ j < 128, ‖samples j -
      F29 (c29 + ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j)‖ ≤ 1 / 10 ^ 72)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples discriminant23Height29Root 128 k -
      discriminant23Height29ScaledModelCoeff k‖ ≤ 1 / 10 ^ 72)
    (w : ℂ) (hw : w ∈ closedBall c29 ρ29) :
    ‖F29 w - dottieRationalWeight c29 discriminant23Height29Model w‖ ≤ 2 / 10 ^ 68 :=
  (discriminant23_height29_model_error_le_finite_budget samples hSample hRound w hw).trans
    (by norm_num [discriminant23Height29CircleErrorBudget])

/-- Dedekind and Hecke nonvanishing at the same input from finite reading data. -/
theorem discriminant23_height29_ne_zero_of_finite_enclosures
    (samples : ℕ → ℂ)
    (hSample : ∀ j < 128, ‖samples j -
      F29 (c29 + ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j)‖ ≤ 1 / 10 ^ 72)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples discriminant23Height29Root 128 k -
      discriminant23Height29ScaledModelCoeff k‖ ≤ 1 / 10 ^ 72)
    {w : ℂ} (hw : w ∈ closedBall c29 ρ29) :
    mixedThetaContinuation L23 w ≠ 0 ∧
      mixedThetaContinuation F23 w ≠ 0 ∧ discriminant23CharacterFold w ≠ 0 := by
  have hE := discriminant23_height29_model_error_of_finite_enclosures samples hSample hRound
  exact ⟨discriminant23_height29_dottie_ne_zero_of_model_error hE hw,
    discriminant23_height29_factors_ne_zero_of_model_error hE hw⟩

/-- The weighted margin allows the readings to be enclosed with a wider tolerance. -/
theorem discriminant23_height29_ne_zero_of_coarser_sample_enclosures
    (samples : ℕ → ℂ)
    (hSample : ∀ j < 128, ‖samples j -
      F29 (c29 + ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j)‖ ≤ 1 / 10 ^ 60)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples discriminant23Height29Root 128 k -
      discriminant23Height29ScaledModelCoeff k‖ ≤ 1 / 10 ^ 72)
    {w : ℂ} (hw : w ∈ closedBall c29 ρ29) :
    mixedThetaContinuation L23 w ≠ 0 ∧
      mixedThetaContinuation F23 w ≠ 0 ∧ discriminant23CharacterFold w ≠ 0 := by
  have hE (z : ℂ) (hz : z ∈ closedBall c29 ρ29) :
      ‖F29 z - dottieRationalWeight c29 discriminant23Height29Model z‖ ≤ 2 / 10 ^ 60 :=
    (discriminant23_height29_model_error_le_finite_budget samples hSample hRound z hz).trans
      (by norm_num [discriminant23Height29CircleErrorBudget])
  have hBudget : (29 : ℝ) / 50 + (3 * 10 ^ 58) * (2 / 10 ^ 60) < 1 := by norm_num
  exact ⟨discriminant23_height29_dottie_ne_zero_of_error_budget hE hBudget hw,
    discriminant23_height29_factors_ne_zero_of_error_budget hE hBudget hw⟩

#check @discriminant23_height29_ne_zero_of_finite_enclosures
#check @discriminant23_height29_ne_zero_of_coarser_sample_enclosures
#print axioms discriminant23_height29_root_primitive
#print axioms discriminant23_height29_model_holomorphic
#print axioms discriminant23_height29_cauchy_bound
#print axioms discriminant23_height29_model_error_le_finite_budget
#print axioms discriminant23_height29_model_error_of_finite_enclosures
#print axioms discriminant23_height29_ne_zero_of_finite_enclosures
#print axioms discriminant23_height29_ne_zero_of_coarser_sample_enclosures

end
end FieldTarget
