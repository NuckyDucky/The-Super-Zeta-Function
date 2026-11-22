import Mathlib.Analysis.Complex.Basic

namespace SuperZeta.QuarterGaussianContrast
noncomputable section

/-- Difference of the reciprocal lengths of the two spectral readings. -/
def scaleGap (ZR ZL : ℂ) : ℝ := 1/‖ZR‖ - 1/‖ZL‖

theorem scaleGap_pos {ZR ZL : ℂ} (hr : 0 < ‖ZR‖) (horder : ‖ZR‖ < ‖ZL‖) :
    0 < scaleGap ZR ZL :=
  sub_pos.mpr (one_div_lt_one_div_of_lt hr horder)

/-- Reflection equates the original Gaussian magnitudes. The oriented spectral
divisors give an exact signed difference between their normalized magnitudes. -/
theorem contrast_eq {GR GL ZR ZL : ℂ} (hreflect : ‖GR‖ = ‖GL‖) :
    ‖GR/ZR‖ - ‖GL/ZL‖ = ‖GR‖*(1/‖ZR‖ - 1/‖ZL‖) := by
  rw [norm_div, norm_div, ← hreflect]
  ring

theorem contrast_pos_iff {GR GL ZR ZL : ℂ} (hreflect : ‖GR‖ = ‖GL‖)
    (hr : 0 < ‖ZR‖) (horder : ‖ZR‖ < ‖ZL‖) :
    0 < ‖GR/ZR‖ - ‖GL/ZL‖ ↔ GR ≠ 0 := by
  rw [contrast_eq hreflect]
  change 0 < ‖GR‖*scaleGap ZR ZL ↔ GR ≠ 0
  rw [mul_pos_iff_of_pos_right (scaleGap_pos hr horder), norm_pos_iff]

theorem contrast_zero_iff {GR GL ZR ZL : ℂ} (hreflect : ‖GR‖ = ‖GL‖)
    (hr : 0 < ‖ZR‖) (horder : ‖ZR‖ < ‖ZL‖) :
    ‖GR/ZR‖ - ‖GL/ZL‖ = 0 ↔ GR = 0 := by
  rw [contrast_eq hreflect]
  change ‖GR‖*scaleGap ZR ZL = 0 ↔ GR = 0
  simp [mul_eq_zero, (scaleGap_pos hr horder).ne']

/-- A certified interval for the common reflected magnitude transports to the
same interval multiplied by the positive scale gap. -/
theorem contrast_bounds {GR GL ZR ZL : ℂ} {lo hi : ℝ} (hreflect : ‖GR‖ = ‖GL‖)
    (hr : 0 < ‖ZR‖) (horder : ‖ZR‖ < ‖ZL‖) (hl : lo ≤ ‖GR‖) (hu : ‖GR‖ ≤ hi) :
    lo*scaleGap ZR ZL ≤ ‖GR/ZR‖-‖GL/ZL‖ ∧
      ‖GR/ZR‖-‖GL/ZL‖ ≤ hi*scaleGap ZR ZL := by
  rw [contrast_eq hreflect]
  have h := (scaleGap_pos hr horder).le
  exact ⟨mul_le_mul_of_nonneg_right hl h, mul_le_mul_of_nonneg_right hu h⟩

/-- For a reflected approximation and a reflected full reading, the error in
the contrast is bounded by the original complex error times the same scale gap. -/
theorem contrast_error {GR GL AR AL ZR ZL : ℂ} {δ : ℝ}
    (hG : ‖GR‖ = ‖GL‖) (hA : ‖AR‖ = ‖AL‖) (hr : 0 < ‖ZR‖)
    (horder : ‖ZR‖ < ‖ZL‖) (herr : ‖GR-AR‖ ≤ δ) :
    |(‖GR/ZR‖-‖GL/ZL‖) - (‖AR/ZR‖-‖AL/ZL‖)| ≤ δ*scaleGap ZR ZL := by
  rw [contrast_eq hG, contrast_eq hA, ← sub_mul, abs_mul]
  change |‖GR‖-‖AR‖| * |scaleGap ZR ZL| ≤ _
  have h := (scaleGap_pos hr horder).le
  rw [abs_of_nonneg h]
  exact mul_le_mul_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans herr) h

/-- The symmetric error test for the contrast has exactly the original cutoff. -/
theorem contrast_exceeds_error_iff {AR AL ZR ZL : ℂ} {δ : ℝ}
    (hA : ‖AR‖ = ‖AL‖) (hr : 0 < ‖ZR‖) (horder : ‖ZR‖ < ‖ZL‖) :
    δ*scaleGap ZR ZL < ‖AR/ZR‖-‖AL/ZL‖ ↔ δ < ‖AR‖ := by
  rw [contrast_eq hA]
  exact mul_lt_mul_right (scaleGap_pos hr horder)

end
end SuperZeta.QuarterGaussianContrast
