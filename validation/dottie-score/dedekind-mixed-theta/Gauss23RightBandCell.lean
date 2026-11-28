import Gauss23RectangleCover
import DedekindDiscriminant23RightStripCount

/-! An integer certificate for a full-strip count increment using right-side rectangles. -/

namespace FieldTarget

open Set DottieOriented.NativeSpectrum.MellinFixed

inductive Gauss23RightCellCover where
  | nonvanishing (whole : Gauss23Cover)
  | crossing (positive : Bool) (slope exterior : Gauss23Cover)

namespace Gauss23RightCellCover

def increment : Gauss23RightCellCover → ℕ
  | .nonvanishing _ => 0
  | .crossing .. => 1

private def rectangle (lo hi left right : ℤ) : Gauss23Rectangle := ⟨left, right, lo, hi⟩

private def endpointBox (value : ℕ → ComplexBox) (m : ℕ) (y : ℤ) : ComplexBox :=
  (rectangle y y 16 16).polynomialBox value false m

private def checkBody (margin : ℤ) (value : ℕ → ComplexBox) (m : ℕ) (lo hi : ℤ) :
    Gauss23RightCellCover → Bool
  | .nonvanishing whole => whole.checkWithMargin margin value m none (rectangle lo hi 16 28)
  | .crossing positive slope exterior =>
    decide (gauss23BoxClearsMargin margin false positive (endpointBox value m lo)) &&
      (decide (gauss23BoxClearsMargin margin false (!positive) (endpointBox value m hi)) &&
        (slope.checkWithMargin margin value m (some positive) (rectangle lo hi 16 20) &&
          exterior.checkWithMargin margin value m none (rectangle lo hi 20 28)))

def check (ceiling : ℕ) (margin : ℤ) (value : ℕ → ComplexBox) (m : ℕ) (lo hi : ℤ)
    (cover : Gauss23RightCellCover) : Bool :=
  decide (0 ≤ lo ∧ lo < hi ∧ hi ≤ 32 * (ceiling : ℤ) ∧ 32 * (m : ℤ) - 16 ≤ lo ∧
    hi ≤ 32 * (m : ℤ) + 16) && checkBody margin value m lo hi cover

theorem sound (ceiling : ℕ) (margin : ℤ) (value : ℕ → ComplexBox) (m : ℕ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (value k) (gauss23CenteredCoeff false (m : ℝ) k))
    (lo hi : ℤ) (cover : Gauss23RightCellCover)
    (hApprox : ∀ (slope : Bool) (w : ℂ), w.re ∈ Icc (1 / 2 : ℝ) (7 / 8) →
      |w.im| ≤ (ceiling : ℝ) → |w.im - (m : ℝ)| ≤ 1 / 2 →
        ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
          gauss23CenteredTaylor slope (m : ℝ) 36 w‖ < (margin : ℝ) / (scale : ℝ))
    (hCheck : cover.check ceiling margin value m lo hi = true) :
    discriminant23CharacterCountingFunction.HasStripZeroIncrement ((lo : ℝ) / 32) ((hi : ℝ) / 32)
      cover.increment := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hCheck
  obtain ⟨⟨hlo, hlt, hhi, hmlo, hmhi⟩, hBody⟩ := hCheck
  have ha : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hab : (lo : ℝ) < hi := by exact_mod_cast hlt
  have hUpper : (hi : ℝ) ≤ 32 * (ceiling : ℝ) := by exact_mod_cast hhi
  have hNearLo : 32 * (m : ℝ) - 16 ≤ (lo : ℝ) := by exact_mod_cast hmlo
  have hNearHi : (hi : ℝ) ≤ 32 * (m : ℝ) + 16 := by exact_mod_cast hmhi
  have hHeight {y : ℝ} (hy : y ∈ Icc ((lo : ℝ) / 32) ((hi : ℝ) / 32)) :
      |y| ≤ (ceiling : ℝ) ∧ |y - (m : ℝ)| ≤ 1 / 2 := by
    rcases hy with ⟨hl, hh⟩
    have hc : 0 ≤ (ceiling : ℝ) := by positivity
    exact ⟨abs_le.mpr ⟨by linarith only [ha, hl, hc], by linarith only [hh, hUpper]⟩,
      abs_le.mpr ⟨by linarith only [hl, hNearLo], by linarith only [hh, hNearHi]⟩⟩
  have hRun (tree : Gauss23Cover) (mode : Option Bool) (left right : ℤ)
      (hTree : tree.checkWithMargin margin value m mode (rectangle lo hi left right) = true)
      {w : ℂ} (hx : w.re ∈ Icc (1 / 2 : ℝ) (7 / 8))
      (hx' : w.re ∈ Icc ((left : ℝ) / 32) ((right : ℝ) / 32))
      (hy : w.im ∈ Icc ((lo : ℝ) / 32) ((hi : ℝ) / 32)) : Gauss23Cover.conclusion mode w := by
    obtain ⟨hT, hm⟩ := hHeight hy
    exact Gauss23Cover.soundOfError margin value m hValue mode tree
      (hApprox mode.isSome w hx hT hm) hTree ⟨hx'.1, hx'.2, hy.1, hy.2⟩
  have hEnd (y : ℤ) (positive : Bool)
      (hy : (y : ℝ) / 32 ∈ Icc ((lo : ℝ) / 32) ((hi : ℝ) / 32))
      (hSign : gauss23BoxClearsMargin margin false positive (endpointBox value m y)) :
      let w : ℂ := ⟨1 / 2, (y : ℝ) / 32⟩
      if positive then 0 < (discriminant23CharacterFold w).re else (discriminant23CharacterFold w).re < 0 := by
    let w : ℂ := ⟨1 / 2, (y : ℝ) / 32⟩
    have hBox : (rectangle y y 16 16).Contains w := by
      norm_num [Gauss23Rectangle.Contains, rectangle, w]
    obtain ⟨hT, hm⟩ := hHeight hy
    have hx : w.re ∈ Icc (1 / 2 : ℝ) (7 / 8) := by norm_num [w]
    have hE := gauss23_sign_of_enclosure margin false false positive (m : ℝ)
      (hApprox false w hx hT hm) (Gauss23Rectangle.polynomialBox_contains value m hValue false hBox) hSign
    simpa only [w, gauss23Coordinate, Bool.false_eq_true, ↓reduceIte] using hE
  cases cover with
  | nonvanishing tree =>
    apply discriminant23_strip_increment_of_right_nonvanishing (by linarith only [hab])
    intro w hx hy
    exact hRun tree none 16 28 hBody hx (by norm_num; exact hx) ⟨hy.1.le, hy.2⟩
  | crossing positive slope exterior =>
    simp only [checkBody, Bool.and_eq_true, decide_eq_true_eq] at hBody
    let d : ℝ := if positive then 1 else -1
    have hab' : (lo : ℝ) / 32 < (hi : ℝ) / 32 := by linarith only [hab]
    have hA := hEnd lo positive ⟨le_rfl, hab'.le⟩ hBody.1
    have hB := hEnd hi (!positive) ⟨hab'.le, le_rfl⟩ hBody.2.1
    apply discriminant23_strip_increment_of_right_crossing (d := d) (by linarith only [ha]) hab'
    · cases positive <;> simpa [d] using hA
    · cases positive <;> simpa [d] using hB
    · intro w hx hy
      have hx' : w.re ∈ Icc (1 / 2 : ℝ) (7 / 8) := ⟨hx.1, by linarith only [hx.2]⟩
      have h := hRun slope (some positive) 16 20 hBody.2.2.1 hx' (by norm_num; exact hx) hy
      cases positive <;> simpa [d, Gauss23Cover.conclusion] using h
    · intro w hx hy
      have hx' : w.re ∈ Icc (1 / 2 : ℝ) (7 / 8) := ⟨by linarith only [hx.1], hx.2⟩
      exact hRun exterior none 20 28 hBody.2.2.2 hx' (by norm_num; exact hx) hy

#print axioms Gauss23RightCellCover.sound

end Gauss23RightCellCover

end FieldTarget
