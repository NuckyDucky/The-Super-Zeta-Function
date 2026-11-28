import DedekindWeightedDottieFullReadings
import DedekindDiscriminant23DottieReading

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

local notation "L23" => Discriminant23GaloisField
local notation "T29" => (29 + 1 / 512 : ℝ)
local notation "c29" => dottieScaledRightCenter T29 0
local notation "r29" => dottieScaledRadius 0
local notation "ρ29" => dottieWeightOuterRadius 0

theorem discriminant23_height29_dottie_geometry :
    c29 = (3 / 4 : ℂ) + 29 * I ∧ r29 = 31 / 128 ∧ ρ29 = 63 / 256 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext <;>
      norm_num [dottieScaledRightCenter, dottieRingScale, Complex.mul_re, Complex.mul_im]
  · norm_num [dottieScaledRadius, dottieRingScale]
  · norm_num [dottieWeightOuterRadius, dottieRingScale]

/-- The two rounded polynomials from the interval replay supply these four
bounds. The exact budget gives a certificate on the actual Dedekind reading. -/
theorem discriminant23_height29_dottie_ne_zero_of_enclosures
    (a : Fin 49 → ℚ × ℚ) (b : Fin 113 → ℚ × ℚ)
    (hB : ∀ z ∈ closedBall c29 ρ29,
      ‖8 * discriminant23CompletedClassProduct z‖ ≤ 4 / 10 ^ 56)
    (hC : dottieWeightCoefficientBound a ρ29 ≤ 3 * 10 ^ 58)
    (hE : ∀ z ∈ closedBall c29 ρ29,
      ‖8 * discriminant23CompletedClassProduct z - dottieRationalWeight c29 b z‖ ≤ 2 / 10 ^ 68)
    (hD : ∀ z ∈ closedBall c29 r29,
      ‖dottieRationalWeight c29 a z * dottieRationalWeight c29 b z + I‖ ≤ 32 / 125)
    {w : ℂ} (hw : w ∈ closedBall c29 r29) : mixedThetaContinuation L23 w ≠ 0 := by
  have hEq (z : ℂ) (hz : z ∈ closedBall c29 ρ29) :
      mixedThetaCompletedReading L23 z = 8 * discriminant23CompletedClassProduct z := by
    obtain ⟨_, hlo, hhi⟩ := dottieWeightOuterRadius_geometry T29 0
    have hDist : ‖z - c29‖ ≤ ρ29 := (dist_eq_norm z c29) ▸ mem_closedBall.mp hz
    have hRe := abs_le.mp ((abs_re_le_norm (z - c29)).trans hDist)
    rw [sub_re] at hRe
    exact discriminant23_completedReading_eq_classProduct z
      (by linarith only [hlo, hRe.1]) (by linarith only [hhi, hRe.2])
  have hCert := dottie_weighted_certificate_of_uniform_model L23
    (T := T29) (n := 0) (m := 1048576) (margin := 3 / 5)
    a (dottieRationalWeight c29 b) (by norm_num) (by norm_num)
    (fun z hz ↦ (hEq z hz).symm ▸ hB z hz) hC
    (fun z hz ↦ (hEq z hz).symm ▸ hE z hz) hD (by norm_num)
  exact mixedTheta_ne_zero_of_dottie_weighted_samples L23 ⟨_, hCert⟩ hw

#check @discriminant23_height29_dottie_ne_zero_of_enclosures
#print axioms discriminant23_height29_dottie_geometry
#print axioms discriminant23_height29_dottie_ne_zero_of_enclosures

end FieldTarget
