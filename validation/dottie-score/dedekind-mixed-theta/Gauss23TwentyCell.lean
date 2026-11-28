import Gauss23RectangleCover
import DedekindDiscriminant23TwentyBand

/-! Check the full rectangle, or a crossing with two exterior rectangles. -/

namespace FieldTarget

open Set DottieOriented.NativeSpectrum.MellinFixed

def gauss23TwentyAnchor (k : ℕ) : ℕ := 10 + k / 16

def gauss23TwentyRectangle (k : ℕ) (left right : ℤ) : Gauss23Rectangle :=
  ⟨left, right, 304 + 2 * (k : ℤ), 304 + 2 * ((k + 1 : ℕ) : ℤ)⟩

private theorem height_units (k : ℕ) :
    ((304 + 2 * (k : ℤ) : ℤ) : ℝ) / 32 = discriminant23TwentyHeight k := by
  simp only [discriminant23TwentyHeight, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  ring

private theorem rectangle_contains (k : ℕ) (left right : ℤ) {w : ℂ}
    (hx : w.re ∈ Icc ((left : ℝ) / 32) ((right : ℝ) / 32))
    (hy : w.im ∈ Icc (discriminant23TwentyHeight k) (discriminant23TwentyHeight (k + 1))) :
    (gauss23TwentyRectangle k left right).Contains w := by
  simpa only [Gauss23Rectangle.Contains, gauss23TwentyRectangle, height_units] using
    And.intro hx.1 (And.intro hx.2 (And.intro hy.1 hy.2))

private theorem height_bounds {k : ℕ} (hk : k < 168) {y : ℝ}
    (hy : y ∈ Icc (discriminant23TwentyHeight k) (discriminant23TwentyHeight (k + 1))) :
    |y| ≤ 20 ∧ |y - (gauss23TwentyAnchor k : ℝ)| ≤ 1 / 2 := by
  have hMax : ((k + 1 : ℕ) : ℝ) ≤ 168 := by exact_mod_cast (show k + 1 ≤ 168 by omega)
  have hMin : 0 ≤ (k : ℝ) := by positivity
  have hMod₀ : 0 ≤ (k % 16 : ℕ) := by omega
  have hMod₁ : k % 16 ≤ 15 := by omega
  have hMod : ((k % 16 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast hMod₁
  have hDecomp : ((k % 16 : ℕ) : ℝ) + 16 * ((k / 16 : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k 16
  have hModReal : (0 : ℝ) ≤ ((k % 16 : ℕ) : ℝ) := by exact_mod_cast hMod₀
  rcases hy with ⟨ha, hb⟩
  unfold discriminant23TwentyHeight at ha hb
  unfold gauss23TwentyAnchor
  push_cast at hb hMax ⊢
  exact ⟨abs_le.mpr ⟨by linarith only [ha, hMin], by linarith only [hb, hMax]⟩,
    abs_le.mpr ⟨by linarith only [ha, hDecomp, hModReal],
      by linarith only [hb, hDecomp, hMod]⟩⟩

inductive Gauss23CellCover where
  | nonvanishing (whole : Gauss23Cover)
  | crossing (slope left right : Gauss23Cover)

namespace Gauss23CellCover

def check (value : ℕ → ComplexBox) (k : ℕ) : Gauss23CellCover → Bool
  | nonvanishing whole =>
    decide (discriminant23TwentyDirection k = 0) &&
      whole.check value (gauss23TwentyAnchor k) none (gauss23TwentyRectangle k 0 32)
  | crossing slope left right =>
    let m := gauss23TwentyAnchor k
    let d := discriminant23TwentyDirection k
    decide (d = 1 ∨ d = -1) &&
      (slope.check value m (some (decide (d = 1))) (gauss23TwentyRectangle k 12 20) &&
        (left.check value m none (gauss23TwentyRectangle k 0 12) &&
          right.check value m none (gauss23TwentyRectangle k 20 32)))

theorem sound (value : ℕ → ComplexBox) {k : ℕ} (hk : k < 168)
    (hValue : ∀ j ≤ 36, ComplexBox.Contains (value j)
      (gauss23CenteredCoeff false (gauss23TwentyAnchor k : ℝ) j))
    (cover : Gauss23CellCover) (hCheck : cover.check value k = true) :
    Discriminant23TwentyCellCondition k := by
  let m := gauss23TwentyAnchor k
  let d := discriminant23TwentyDirection k
  have hRun (tree : Gauss23Cover) (sign : Option Bool) (left right : ℤ)
      (hTree : tree.check value m sign (gauss23TwentyRectangle k left right) = true)
      {w : ℂ} (hx : w.re ∈ Icc (0 : ℝ) 1)
      (hx' : w.re ∈ Icc ((left : ℝ) / 32) ((right : ℝ) / 32))
      (hy : w.im ∈ Icc (discriminant23TwentyHeight k) (discriminant23TwentyHeight (k + 1))) :
      Gauss23Cover.conclusion sign w := by
    obtain ⟨h₁, h₂⟩ := height_bounds hk hy
    exact Gauss23Cover.sound value m hValue sign tree hx.1 hx.2 h₁ h₂ hTree
      (rectangle_contains k left right hx' hy)
  unfold Discriminant23TwentyCellCondition
  dsimp only
  cases cover with
  | nonvanishing tree =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hCheck
    rw [ite_eq_left hCheck.1]
    intro w hx hy
    have hx' : w.re ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    exact hRun tree none 0 32 hCheck.2 hx' (by simpa using hx') ⟨hy.1.le, hy.2⟩
  | crossing slope left right =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hCheck
    have hd : d = 1 ∨ d = -1 := hCheck.1
    have hd₀ : d ≠ 0 := by rcases hd with h | h <;> rw [h] <;> decide
    rw [ite_eq_right hd₀]
    constructor
    · intro w hx hy
      have hx' : w.re ∈ Icc (0 : ℝ) 1 := ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
      have hs := hRun slope (some (decide (d = 1))) 12 20 hCheck.2.1 hx'
        (by norm_num; exact hx) hy
      change 0 < (d : ℝ) * (deriv discriminant23CharacterFold w).im
      rcases hd with hd | hd
      · simpa [Gauss23Cover.conclusion, hd] using hs
      · have hn : (deriv discriminant23CharacterFold w).im < 0 := by
          simpa [Gauss23Cover.conclusion, hd] using hs
        simpa [hd] using neg_pos.mpr hn
    · intro w hx hy hz
      have hx' : w.re ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      constructor
      · by_contra! hl
        have hleft : w.re ∈ Icc ((0 : ℤ) / (32 : ℝ)) ((12 : ℤ) / (32 : ℝ)) := by
          norm_num
          exact ⟨hx'.1, hl.le⟩
        exact hRun left none 0 12 hCheck.2.2.1 hx' hleft hy hz
      · by_contra! hr
        have hright : w.re ∈ Icc ((20 : ℤ) / (32 : ℝ)) ((32 : ℤ) / (32 : ℝ)) := by
          norm_num
          exact ⟨hr.le, hx'.2⟩
        exact hRun right none 20 32 hCheck.2.2.2 hx' hright hy hz

end Gauss23CellCover

#print axioms Gauss23CellCover.sound

end FieldTarget
