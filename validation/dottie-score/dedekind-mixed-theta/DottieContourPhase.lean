import DedekindCofinalSignedRings

namespace FieldTarget

open Complex Set SuperZeta.StirlingCorrection

/-- The oriented determinant of two complex readings. -/
def contourCross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- Three readings whose successive turns have positive determinants cannot
all have strictly negative imaginary part under the same rotation. -/
theorem no_signed_axis_of_positive_turns {u v w : ℂ}
    (huv : 0 < contourCross u v) (hvw : 0 < contourCross v w)
    (hwu : 0 < contourCross w u) (axis : ℂ) :
    ¬ ((axis * u).im < 0 ∧ (axis * v).im < 0 ∧ (axis * w).im < 0) := by
  rintro ⟨hu, hv, hw⟩
  have hid : contourCross v w * (axis * u).im + contourCross w u * (axis * v).im +
      contourCross u v * (axis * w).im = 0 := by
    simp only [contourCross, mul_im]
    ring
  have hsum := add_neg (add_neg (mul_neg_of_pos_of_neg hvw hu) (mul_neg_of_pos_of_neg hwu hv))
    (mul_neg_of_pos_of_neg huv hw)
  rw [hid] at hsum
  exact (lt_irrefl 0) hsum

/-- A holomorphic weight can correct phase along the measuring contour.
Every zero of the original reading would still be a zero of the product. -/
theorem dottie_disk_nonzero_of_holomorphic_weight {F W : ℂ → ℂ} {T margin : ℝ}
    {n : ℕ} (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hm : 0 < margin)
    (hboundary : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (W z * F z).im ≤ -margin)
    {w : ℂ} (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    F w ≠ 0 := by
  have h := dottie_disk_nonzero_of_signed_boundary (axis := 1) (hW.mul hF) hm
    (fun z hz => by simpa only [Pi.mul_apply, one_mul] using hboundary z hz) hw
  intro hz
  exact h (by simp [hz])

#print axioms no_signed_axis_of_positive_turns
#print axioms dottie_disk_nonzero_of_holomorphic_weight

end FieldTarget
