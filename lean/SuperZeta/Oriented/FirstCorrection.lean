import SuperZeta.Oriented.TraceRecovery

/-!
# The first coefficient relative to the cosine-product reference

The comparison is the difference of the two normalized logarithmic-derivative
coefficients at zero.
-/

namespace DottieOriented.TraceRecovery

noncomputable section

/-- Remove the dynamical terms from the determinant, keeping the phase. -/
def referenceDet (φ : ℝ) (v : ℂ) : ℂ :=
  signedDet 0 φ v + v / (Real.cos φ : ℂ) ^ 2

theorem referenceDet_sq (φ : ℝ) (z : ℂ) :
    referenceDet φ (z ^ 2) =
      Complex.cos (z - (φ : ℂ)) * Complex.cos (z + (φ : ℂ)) / (Real.cos φ : ℂ) ^ 2 := by
  rw [referenceDet, signedDet_sq_expanded]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  calc
    _ = (Complex.cos z ^ 2 - (Real.sin φ : ℂ) ^ 2) / (Real.cos φ : ℂ) ^ 2 := by ring
    _ = _ := by
      congr 1
      have hz := Complex.cos_sq_add_sin_sq z
      have hφ : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq φ
      rw [Complex.cos_sub, Complex.cos_add, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      linear_combination -(Complex.cos z ^ 2) * hφ + (Real.sin φ : ℂ) ^ 2 * hz

theorem signedDet_sub_referenceDet_sq (σ φ : ℝ) (z : ℂ) :
    signedDet σ φ (z ^ 2) - referenceDet φ (z ^ 2) =
      (-(z ^ 2) + 2 * (σ : ℂ) * (Real.sin φ : ℂ) * (z * Complex.sin z)) /
        (Real.cos φ : ℂ) ^ 2 := by
  rw [referenceDet, signedDet_sq_expanded, signedDet_sq_expanded]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring

theorem referenceDet_analytic (φ : ℝ) (v : ℂ) : AnalyticAt ℂ (referenceDet φ) v := by
  unfold referenceDet
  simp only [div_eq_mul_inv]
  exact (signedDet_analytic 0 φ v).add (analyticAt_id.mul analyticAt_const)

theorem referenceDet_at_zero {φ : ℝ} (hφ : Real.cos φ ≠ 0) : referenceDet φ 0 = 1 := by
  simp only [referenceDet, zero_div, add_zero, signedDet_at_zero hφ]

theorem referenceDet_hasDerivAt_zero (φ : ℝ) :
    HasDerivAt (referenceDet φ) (((-1) / Real.cos φ ^ 2 : ℝ) : ℂ) 0 := by
  have h := (signedDet_hasDerivAt_zero 0 φ).add
    ((hasDerivAt_id' (0 : ℂ)).div_const ((Real.cos φ : ℂ) ^ 2))
  convert h using 1
  push_cast
  ring

/-- The first reference trace coefficient for a normalized reference. -/
def referenceFirstTrace (φ : ℝ) : ℝ := -(deriv (referenceDet φ) 0).re

theorem referenceFirstTrace_eq (φ : ℝ) : referenceFirstTrace φ = 1 / Real.cos φ ^ 2 := by
  rw [referenceFirstTrace, (referenceDet_hasDerivAt_zero φ).deriv, Complex.ofReal_re]
  ring

def firstCorrection (φ : ℝ) : ℝ := firstTrace 1 φ - referenceFirstTrace φ

theorem firstCorrection_eq (φ : ℝ) :
    firstCorrection φ = (1 - 2 * Real.sin φ) / Real.cos φ ^ 2 := by
  rw [firstCorrection, firstTrace, (signedDet_hasDerivAt_zero 1 φ).deriv,
    Complex.ofReal_re, referenceFirstTrace_eq]
  ring

theorem firstCorrection_pi_div_six :
    firstTrace 1 (Real.pi / 6) = 4 / 3 ∧ referenceFirstTrace (Real.pi / 6) = 4 / 3 ∧
      firstCorrection (Real.pi / 6) = 0 := by
  have hφ : Real.cos (Real.pi / 6) ≠ 0 := by rw [Real.cos_pi_div_six]; positivity
  have hm : firstTrace 1 (Real.pi / 6) = 4 / 3 := by
    rw [firstTrace_eq (by norm_num) hφ, Real.sin_pi_div_six]
    norm_num
  have hr : referenceFirstTrace (Real.pi / 6) = 4 / 3 := by
    rw [referenceFirstTrace_eq, Real.sq_cos_pi_div_six]
    norm_num
  exact ⟨hm, hr, by rw [firstCorrection, hm, hr, sub_self]⟩

theorem firstCorrection_neg_pi_div_six :
    firstTrace 1 (-(Real.pi / 6)) = 4 ∧ referenceFirstTrace (-(Real.pi / 6)) = 4 / 3 ∧
      firstCorrection (-(Real.pi / 6)) = 8 / 3 := by
  have hφ : Real.cos (-(Real.pi / 6)) ≠ 0 := by
    rw [Real.cos_neg, Real.cos_pi_div_six]
    positivity
  have hm : firstTrace 1 (-(Real.pi / 6)) = 4 := by
    rw [firstTrace_eq (by norm_num) hφ, Real.sin_neg, Real.sin_pi_div_six]
    norm_num
  have hr : referenceFirstTrace (-(Real.pi / 6)) = 4 / 3 := by
    rw [referenceFirstTrace_eq, Real.cos_neg, Real.sq_cos_pi_div_six]
    norm_num
  exact ⟨hm, hr, by rw [firstCorrection, hm, hr]; norm_num⟩

end

end DottieOriented.TraceRecovery
