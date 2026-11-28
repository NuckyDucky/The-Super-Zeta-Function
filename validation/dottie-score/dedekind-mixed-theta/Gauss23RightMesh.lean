import Gauss23RightBandCell
import Gauss23RightValues

/-! The right-side mesh from height 20 through 447/16. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

private def rightCovers : Array Gauss23RightCellCover := #[
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .crossing false (.leaf true false) (.leaf true false),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf false true)) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf true true)) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.splitReal 17 (.leaf false true) (.leaf true true)) (.leaf true true)) (.leaf true true)),
  .crossing true (.leaf true true) (.leaf true true),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf false false)) (.leaf false false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf false false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf false false)),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf true false)) (.leaf true false)),
  .crossing false (.leaf true false) (.leaf true false),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf true true)) (.leaf true true)),
  .crossing true (.leaf true true) (.leaf true true),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf false false)) (.leaf false false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf false false)),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf true false)) (.leaf true false)),
  .crossing false (.leaf true false) (.leaf true false),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf false true)) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.splitReal 17 (.leaf false true) (.leaf true true)) (.leaf true true)) (.leaf true true)),
  .crossing true (.leaf true true) (.leaf true true),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf false false)) (.leaf false false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf false false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf false false)),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.leaf false false),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.leaf false false) (.leaf true false)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false false) (.leaf true false)) (.leaf true false)),
  .crossing false (.leaf true false) (.splitReal 24 (.leaf true false) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf false true)) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf false true)),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.leaf false true),
  .nonvanishing (.splitReal 22 (.leaf false true) (.leaf true true)),
  .nonvanishing (.splitReal 22 (.splitReal 19 (.leaf false true) (.leaf true true)) (.leaf true true))
]

def gauss23RightCover (k : ℕ) : Gauss23RightCellCover :=
  rightCovers.getD k (.nonvanishing (.leaf false false))

/-- Skip the cut at 109/4 so its two neighboring cells form one bracket. -/
def gauss23RightOrdinal (k : ℕ) : ℕ := k + if 116 ≤ k then 1 else 0

def gauss23RightCut (k : ℕ) : ℤ := 640 + 2 * (gauss23RightOrdinal k : ℤ)

noncomputable def gauss23RightHeight (k : ℕ) : ℝ := (gauss23RightCut k : ℝ) / 32

def gauss23RightCheck (m k : ℕ) : Bool :=
  (gauss23RightCover k).check 28 100 (gauss23RightValue m) m (gauss23RightCut k) (gauss23RightCut (k + 1))

theorem gauss23_right_segment_of_checks (m start len : ℕ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (gauss23RightValue m k)
        (gauss23CenteredCoeff false (m : ℝ) k))
    (hCheck : ∀ j : Fin len, gauss23RightCheck m (start + j.val) = true) (j : Fin len) :
    discriminant23CharacterCountingFunction.HasStripZeroIncrement (gauss23RightHeight (start + j.val))
      (gauss23RightHeight (start + j.val + 1)) (gauss23RightCover (start + j.val)).increment := by
  apply Gauss23RightCellCover.sound 28 100 (gauss23RightValue m) m hValue
    (gauss23RightCut (start + j.val)) (gauss23RightCut (start + j.val + 1)) _ _ (hCheck j)
  intro slope w hx ht hm
  have h := discriminant23_gaussCenteredTaylor_error_lt_of_right_twentyEight slope (m : ℝ) hx.1 hx.2 ht hm
  norm_num [scale] at h ⊢
  exact h

#print axioms gauss23_right_segment_of_checks

end FieldTarget
