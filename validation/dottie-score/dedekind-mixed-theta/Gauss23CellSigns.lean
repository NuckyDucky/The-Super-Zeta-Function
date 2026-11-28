import Gauss23CoefficientIntervals

/-! Resolve a sign of the actual value or slope on a whole offset box. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

def gauss23Coordinate (imaginary : Bool) (z : ℂ) : ℝ :=
  if imaginary then z.im else z.re

def gauss23CoordinateBox (imaginary : Bool) (b : ComplexBox) : Box :=
  if imaginary then b.im else b.re

def gauss23BoxClearsError (imaginary positive : Bool) (box : ComplexBox) : Prop :=
  let reading := gauss23CoordinateBox imaginary box
  if positive then 300000 < reading.lo else reading.hi < -300000

instance (imaginary positive : Bool) (box : ComplexBox) :
    Decidable (gauss23BoxClearsError imaginary positive box) := by
  cases positive <;> simp only [gauss23BoxClearsError, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem gauss23_half_height_sign_of_enclosure (slope imaginary positive : Bool) (t : ℝ) {w : ℂ}
    (hx₀ : 0 ≤ w.re) (hx₁ : w.re ≤ 1) (hy : |w.im| ≤ 20) (ht : |w.im - t| ≤ 1 / 2)
    {box : ComplexBox} (hEnclosure : ComplexBox.Contains box (gauss23CenteredTaylor slope t 36 w))
    (hMargin : gauss23BoxClearsError imaginary positive box) :
    let f := if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w
    if positive then 0 < gauss23Coordinate imaginary f else gauss23Coordinate imaginary f < 0 := by
  let P := gauss23CenteredTaylor slope t 36 w
  let F := if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w
  let B := gauss23CoordinateBox imaginary box
  have hQuad : ‖F - P‖ < (3 / 10 ^ 19 : ℝ) :=
    discriminant23_gaussCenteredTaylor_error_lt_of_half_height slope t hx₀ hx₁ hy ht
  have hC : Contains B (gauss23Coordinate imaginary P) := by
    cases imaginary
    · exact hEnclosure.1
    · exact hEnclosure.2
  have hErr : |gauss23Coordinate imaginary F - gauss23Coordinate imaginary P| <
      (3 / 10 ^ 19 : ℝ) := by
    cases imaginary
    · simpa only [gauss23Coordinate, Bool.false_eq_true, ↓reduceIte, Complex.sub_re] using
        (Complex.abs_re_le_norm (F - P)).trans_lt hQuad
    · simpa only [gauss23Coordinate, ↓reduceIte, Complex.sub_im] using
        (Complex.abs_im_le_norm (F - P)).trans_lt hQuad
  have hScale : (scale : ℝ) * (3 / 10 ^ 19 : ℝ) = 300000 := by norm_num [scale]
  cases positive
  · change B.hi < -300000 at hMargin
    have hM : (B.hi : ℝ) < -(300000 : ℝ) := by exact_mod_cast hMargin
    have hSign := lt_of_box_upper (margin := -(3 / 10 ^ 19 : ℝ)) hC
      (by rw [mul_neg, hScale]; exact hM)
    change gauss23Coordinate imaginary F < 0
    linarith only [hSign, (abs_lt.mp hErr).2]
  · change 300000 < B.lo at hMargin
    have hM : (300000 : ℝ) < (B.lo : ℝ) := by exact_mod_cast hMargin
    have hSign := lt_of_box_lower (margin := (3 / 10 ^ 19 : ℝ)) hC (by rw [hScale]; exact hM)
    change 0 < gauss23Coordinate imaginary F
    linarith only [hSign, (abs_lt.mp hErr).1]

#print axioms gauss23_half_height_sign_of_enclosure

end FieldTarget
