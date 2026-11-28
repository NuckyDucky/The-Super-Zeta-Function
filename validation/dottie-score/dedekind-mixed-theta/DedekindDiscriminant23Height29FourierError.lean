import ContourCircleSamples
import DedekindDiscriminant23Height29Polynomials

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection
open scoped BigOperators NNReal

noncomputable section

local notation "c29" => dottieScaledRightCenter (29 + 1 / 512 : ℝ) 0
local notation "ρ29" => dottieWeightOuterRadius 0
local notation "F29" => (fun w : ℂ ↦ 8 * discriminant23CompletedClassProduct w)

set_option exponentiation.threshold 512

def discriminant23Height29ScaledModelCoeff (k : ℕ) : ℂ :=
  if hk : k < 113 then
    let a := discriminant23Height29Model ⟨k, hk⟩
    ((a.1 : ℝ) + I * (a.2 : ℝ)) * ((1 / 2 : ℝ) : ℂ) ^ k
  else 0

private theorem height29_rounded_polynomial_eq (w : ℂ) :
    (∑ k ∈ Finset.range 113,
      discriminant23Height29ScaledModelCoeff k * ((w - c29) / ((1 / 2 : ℝ) : ℂ)) ^ k) =
      dottieRationalWeight c29 discriminant23Height29Model w := by
  rw [← Fin.sum_univ_eq_sum_range, dottieRationalWeight]
  apply Finset.sum_congr rfl
  intro k _
  rw [discriminant23Height29ScaledModelCoeff, dite_eq_left k.isLt, mul_assoc, ← mul_pow]
  congr 2
  rw [mul_comm, div_mul_cancel₀ _ (by norm_num)]

theorem contourSamplePolynomial_rounding_error_le
    {samples : ℕ → ℂ} {ω z : ℂ} {N n : ℕ} {p : ℕ → ℂ} {r ε : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < 1) (hε : 0 ≤ ε)
    (hRound : ∀ k < n, ‖contourSampleCoeff samples ω N k - p k‖ ≤ ε) :
    ‖contourSamplePolynomial samples ω N n z - ∑ k ∈ Finset.range n, p k * z ^ k‖ ≤
      ε / (1 - r) := by
  have hr₀ : 0 ≤ r := (norm_nonneg z).trans hz
  have hSum : ∑ k ∈ Finset.range n, r ^ k ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr₀ hr]
    exact (summable_geometric_of_lt_one hr₀ hr).sum_le_tsum _ (fun k _ ↦ pow_nonneg hr₀ k)
  rw [contourSamplePolynomial, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range n, ε * r ^ k := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hRound k (Finset.mem_range.mp hk))
        (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) hε
    _ ≤ _ := by
      rw [← Finset.mul_sum, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hSum hε

/-- Taylor truncation, sampling error with aliasing, and rounding on the height-29 disk. -/
def discriminant23Height29CircleErrorBudget (sampleError roundingError : ℝ) : ℝ :=
  2 ^ 27 * (63 / 512 : ℝ) ^ (113 : ℕ) / (1 - 63 / 512) +
    (sampleError + 2 ^ 27 * (1 / 4 : ℝ) ^ (128 : ℕ) / (1 - 1 / 4)) / (1 - 63 / 128) +
    roundingError / (1 - 63 / 128)

/-- The uniform error bound with both finite tolerances left as parameters. -/
theorem discriminant23_height29_model_error_le_circle_budget
    (samples : ℕ → ℂ) {ω : ℂ}
    (hω : IsPrimitiveRoot ω 128) (hUnit : ‖ω‖ = 1)
    (hHol : DifferentiableOn ℂ F29 (closedBall c29 2))
    (hOuter : ∀ z ∈ sphere c29 2, ‖F29 z‖ ≤ 2 ^ 27)
    {sampleError roundingError : ℝ}
    (hSample : ∀ j < 128, ‖samples j - F29 (c29 + ((1 / 2 : ℝ) : ℂ) * ω ^ j)‖ ≤ sampleError)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples ω 128 k - discriminant23Height29ScaledModelCoeff k‖ ≤
      roundingError)
    (w : ℂ) (hw : w ∈ closedBall c29 ρ29) :
    ‖F29 w - dottieRationalWeight c29 discriminant23Height29Model w‖ ≤
      discriminant23Height29CircleErrorBudget sampleError roundingError := by
  have hDist : ‖w - c29‖ ≤ (63 / 256 : ℝ) := by
    have h := mem_closedBall.mp hw
    rwa [dist_eq_norm, discriminant23_height29_dottie_geometry.2.2] at h
  let y := (w - c29) / ((1 / 2 : ℝ) : ℂ)
  have hy : ‖y‖ ≤ (63 / 128 : ℝ) := by
    dsimp [y]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  have hApprox := contourSamplePolynomial_error_le
    (F := F29) (S := samples) (c := c29) (x := w - c29)
    (R := 2) (h := 1 / 2) (r := 63 / 256) (M := 2 ^ 27) (ε := sampleError)
    (N := 128) (n := 113) hHol hOuter (by norm_num) (by norm_num) hω hUnit
    (by norm_num) (by norm_num) hDist hSample
  rw [show c29 + (w - c29) = w by ring] at hApprox
  have hRound₀ : 0 ≤ roundingError := (norm_nonneg _).trans (hRound 0 (by norm_num))
  have hRound' := contourSamplePolynomial_rounding_error_le hy (by norm_num) hRound₀ hRound
  have hEq := height29_rounded_polynomial_eq w
  change (∑ k ∈ Finset.range 113, discriminant23Height29ScaledModelCoeff k * y ^ k) = _ at hEq
  rw [hEq] at hRound'
  refine (norm_sub_le_norm_sub_add_norm_sub _ (contourSamplePolynomial samples ω 128 113 y) _).trans ?_
  refine (add_le_add hApprox hRound').trans ?_
  norm_num [discriminant23Height29CircleErrorBudget]

/-- The error used by the original height-29 model replay. -/
theorem discriminant23_height29_model_error_of_circle_data
    (samples : ℕ → ℂ) {ω : ℂ}
    (hω : IsPrimitiveRoot ω 128) (hUnit : ‖ω‖ = 1)
    (hHol : DifferentiableOn ℂ F29 (closedBall c29 2))
    (hOuter : ∀ z ∈ sphere c29 2, ‖F29 z‖ ≤ 2 ^ 27)
    (hSample : ∀ j < 128, ‖samples j - F29 (c29 + ((1 / 2 : ℝ) : ℂ) * ω ^ j)‖ ≤ 1 / 10 ^ 72)
    (hRound : ∀ k < 113, ‖contourSampleCoeff samples ω 128 k - discriminant23Height29ScaledModelCoeff k‖ ≤
      1 / 10 ^ 72)
    (w : ℂ) (hw : w ∈ closedBall c29 ρ29) :
    ‖F29 w - dottieRationalWeight c29 discriminant23Height29Model w‖ ≤ 2 / 10 ^ 68 :=
  (discriminant23_height29_model_error_le_circle_budget samples hω hUnit hHol hOuter
    hSample hRound w hw).trans (by norm_num [discriminant23Height29CircleErrorBudget])

#check @discriminant23_height29_model_error_of_circle_data
#print axioms contourSamplePolynomial_rounding_error_le
#print axioms discriminant23_height29_model_error_le_circle_budget
#print axioms discriminant23_height29_model_error_of_circle_data

end
end FieldTarget
