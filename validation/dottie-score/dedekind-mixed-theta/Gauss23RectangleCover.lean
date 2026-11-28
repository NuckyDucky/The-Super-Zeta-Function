import Gauss23SharedCoefficients
import Gauss23CellSigns
import Gauss23CenteredHorner

/-! A rectangle certificate uses directed integer arithmetic for its leaves.
The splitting theorem covers every point of the original closed rectangle. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

structure Gauss23Rectangle where
  left : ℤ
  right : ℤ
  bottom : ℤ
  top : ℤ

namespace Gauss23Rectangle

def Contains (r : Gauss23Rectangle) (w : ℂ) : Prop :=
  (r.left : ℝ) / 32 ≤ w.re ∧ w.re ≤ (r.right : ℝ) / 32 ∧
  (r.bottom : ℝ) / 32 ≤ w.im ∧ w.im ≤ (r.top : ℝ) / 32

private def centerRe (r : Gauss23Rectangle) : ℤ := r.left + r.right - 32

private def centerIm (r : Gauss23Rectangle) (m : ℕ) : ℤ := r.bottom + r.top - 64 * (m : ℤ)

private def center (r : Gauss23Rectangle) (m : ℕ) : ComplexBox :=
  ⟨fromRatio r.centerRe 64, fromRatio (r.centerIm m) 64⟩

private def offset (r : Gauss23Rectangle) : ComplexBox :=
  ⟨rangeRatio (r.left - r.right) (r.right - r.left) 64,
    rangeRatio (r.bottom - r.top) (r.top - r.bottom) 64⟩

private def coefficient (value : ℕ → ComplexBox) (slope : Bool) (k : ℕ) : ComplexBox :=
  if k < 36 then gauss23SharedCoefficient value slope k else ComplexBox.zero

def polynomialBox (value : ℕ → ComplexBox) (slope : Bool) (m : ℕ) (r : Gauss23Rectangle) :
    ComplexBox :=
  ComplexBox.centeredHorner (r.center m) r.offset (coefficient value slope) 36

theorem polynomialBox_contains (value : ℕ → ComplexBox) (m : ℕ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (value k) (gauss23CenteredCoeff false (m : ℝ) k))
    (slope : Bool) {r : Gauss23Rectangle} {w : ℂ} (hw : r.Contains w) :
    ComplexBox.Contains (polynomialBox value slope m r) (gauss23CenteredTaylor slope (m : ℝ) 36 w) := by
  let c : ℂ := ⟨(r.centerRe : ℝ) / 64, (r.centerIm m : ℝ) / 64⟩
  let z := w - gauss23CriticalPoint (m : ℝ) - c
  have hc : ComplexBox.Contains (r.center m) c :=
    ⟨ratio_contains r.centerRe (by decide), ratio_contains (r.centerIm m) (by decide)⟩
  have hz : ComplexBox.Contains r.offset z := by
    rcases hw with ⟨hl, hr, hb, ht⟩
    constructor <;> apply rangeRatio_contains (by decide) <;>
      simp only [z, c, gauss23CriticalPoint, Complex.sub_re, Complex.sub_im,
        centerRe, centerIm, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] <;>
      linarith only [hl, hr, hb, ht]
  let a (k : ℕ) : ℂ := if k < 36 then gauss23CenteredCoeff slope (m : ℝ) k else 0
  have ha (k : ℕ) : ComplexBox.Contains (coefficient value slope k) (a k) := by
    by_cases hk : k < 36
    · simpa only [coefficient, a, ite_eq_left hk] using gauss23_sharedCoefficient_contains value (m : ℝ) hValue slope hk
    · simpa only [coefficient, a, ite_eq_right hk] using ComplexBox.zero_contains
  have h := ComplexBox.centeredHorner_contains hc hz (coefficient value slope) a ha 36
  have hz' : c + z = w - gauss23CriticalPoint (m : ℝ) := by dsimp only [z]; abel
  rw [hz'] at h
  have he : (∑ k ∈ Finset.range 36, a k * (w - gauss23CriticalPoint (m : ℝ)) ^ k) =
      gauss23CenteredTaylor slope (m : ℝ) 36 w := by
    unfold gauss23CenteredTaylor
    exact Finset.sum_congr rfl (fun k hk ↦ by simp only [a, ite_eq_left (Finset.mem_range.mp hk)])
  exact he ▸ h

end Gauss23Rectangle

inductive Gauss23Cover where
  | leaf (imaginary positive : Bool)
  | splitReal (cut : ℤ) (left right : Gauss23Cover)
  | splitImaginary (cut : ℤ) (bottom top : Gauss23Cover)

namespace Gauss23Cover

/-- With no slope sign, a leaf may use either coordinate to exclude zero. -/
def checkWithMargin (margin : ℤ) (value : ℕ → ComplexBox) (m : ℕ) (slopeSign : Option Bool)
    (r : Gauss23Rectangle) :
    Gauss23Cover → Bool
  | leaf imaginary positive =>
    let box := r.polynomialBox value slopeSign.isSome m
    decide (gauss23BoxClearsMargin margin (slopeSign.isSome || imaginary) (slopeSign.getD positive) box)
  | splitReal cut left right =>
    checkWithMargin margin value m slopeSign {r with right := cut} left &&
      checkWithMargin margin value m slopeSign {r with left := cut} right
  | splitImaginary cut bottom top =>
    checkWithMargin margin value m slopeSign {r with top := cut} bottom &&
      checkWithMargin margin value m slopeSign {r with bottom := cut} top

abbrev check := checkWithMargin 300000

def conclusion (slopeSign : Option Bool) (w : ℂ) : Prop :=
  match slopeSign with
  | none => discriminant23CharacterFold w ≠ 0
  | some positive =>
    if positive then 0 < (deriv discriminant23CharacterFold w).im
    else (deriv discriminant23CharacterFold w).im < 0

theorem soundOfError (margin : ℤ) (value : ℕ → ComplexBox) (m : ℕ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (value k) (gauss23CenteredCoeff false (m : ℝ) k))
    (slopeSign : Option Bool) (tree : Gauss23Cover) {r : Gauss23Rectangle} {w : ℂ}
    (hApprox : ‖(if slopeSign.isSome then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
      gauss23CenteredTaylor slopeSign.isSome (m : ℝ) 36 w‖ < (margin : ℝ) / (scale : ℝ))
    (hCheck : tree.checkWithMargin margin value m slopeSign r = true) (hw : r.Contains w) :
    conclusion slopeSign w := by
  induction tree generalizing r with
  | leaf imaginary positive =>
    have hMargin : gauss23BoxClearsMargin margin (slopeSign.isSome || imaginary) (slopeSign.getD positive)
        (r.polynomialBox value slopeSign.isSome m) := of_decide_eq_true hCheck
    have h := gauss23_sign_of_enclosure margin slopeSign.isSome
      (slopeSign.isSome || imaginary) (slopeSign.getD positive) (m : ℝ) hApprox
      (Gauss23Rectangle.polynomialBox_contains value m hValue slopeSign.isSome hw) hMargin
    cases slopeSign with
    | none =>
      intro hz
      simp only [Option.isSome_none, Option.getD_none, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hz] at h
      cases imaginary <;> cases positive <;> simp [gauss23Coordinate] at h
    | some s =>
      simpa only [conclusion, Option.isSome_some, Option.getD_some, Bool.true_or, ↓reduceIte,
        gauss23Coordinate] using h
  | splitReal cut left right ihl ihr =>
    simp only [checkWithMargin, Bool.and_eq_true] at hCheck
    rcases hw with ⟨ha, hb, hc, hd⟩
    by_cases hl : w.re ≤ (cut : ℝ) / 32
    · exact ihl hCheck.1 ⟨ha, hl, hc, hd⟩
    · exact ihr hCheck.2 ⟨(lt_of_not_ge hl).le, hb, hc, hd⟩
  | splitImaginary cut bottom top ihb iht =>
    simp only [checkWithMargin, Bool.and_eq_true] at hCheck
    rcases hw with ⟨ha, hb, hc, hd⟩
    by_cases hl : w.im ≤ (cut : ℝ) / 32
    · exact ihb hCheck.1 ⟨ha, hb, hc, hl⟩
    · exact iht hCheck.2 ⟨ha, hb, (lt_of_not_ge hl).le, hd⟩

theorem sound (value : ℕ → ComplexBox) (m : ℕ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (value k) (gauss23CenteredCoeff false (m : ℝ) k))
    (slopeSign : Option Bool) (tree : Gauss23Cover) {r : Gauss23Rectangle} {w : ℂ}
    (hx₀ : 0 ≤ w.re) (hx₁ : w.re ≤ 1) (hy : |w.im| ≤ 20) (hm : |w.im - (m : ℝ)| ≤ 1 / 2)
    (hCheck : tree.check value m slopeSign r = true) (hw : r.Contains w) : conclusion slopeSign w := by
  apply soundOfError 300000 value m hValue slopeSign tree _ hCheck hw
  convert discriminant23_gaussCenteredTaylor_error_lt_of_half_height slopeSign.isSome (m : ℝ) hx₀ hx₁ hy hm
    using 1
  norm_num [scale]

end Gauss23Cover

#print axioms Gauss23Rectangle.polynomialBox_contains
#print axioms Gauss23Cover.soundOfError
#print axioms Gauss23Cover.sound

end FieldTarget
