import ComplexStripCrossingMesh
import DedekindDiscriminant23SevenEighths
import Gauss23StripReflection

/-! Count a full strip band from its right half by reflecting at the same height. -/

namespace FieldTarget

open Complex Set
open scoped ComplexConjugate

private theorem reflected_re (w : ℂ) : (1 - conj w).re = 1 - w.re := by
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]

private theorem reflected_im (w : ℂ) : (1 - conj w).im = w.im := by
  simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]

private theorem character_ne_zero_of_right_or_reflected {w : ℂ} {r : ℝ}
    (hlo : 0 < w.re) (hhi : w.re < 1) (hSide : r ≤ w.re ∨ r ≤ 1 - w.re)
    (hRight : ∀ z : ℂ, r ≤ z.re → z.re ≤ 7 / 8 → z.im = w.im → discriminant23CharacterFold z ≠ 0) :
    discriminant23CharacterFold w ≠ 0 := by
  have hLocal (z : ℂ) (ha : r ≤ z.re) (hb : z.re < 1) (hy : z.im = w.im) :
      discriminant23CharacterFold z ≠ 0 := by
    by_cases hout : z.re ≤ 7 / 8
    · exact hRight z ha hout hy
    · exact discriminant23_character_ne_zero_above_seven_eighths (lt_of_not_ge hout) hb
  rcases hSide with h | h
  · exact hLocal w h hhi rfl
  · intro hz
    apply hLocal (1 - conj w) (by rwa [reflected_re]) (by rw [reflected_re]; linarith only [hlo])
      (reflected_im w)
    rw [discriminant23_characterFold_same_height_reflection, hz, map_zero]

theorem discriminant23_strip_increment_of_right_nonvanishing {a b : ℝ} (hab : a ≤ b)
    (hRight : ∀ w : ℂ, w.re ∈ Icc (1 / 2 : ℝ) (7 / 8) → w.im ∈ Ioc a b →
      discriminant23CharacterFold w ≠ 0) :
    discriminant23CharacterCountingFunction.HasStripZeroIncrement a b 0 := by
  apply discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_ne_zero hab
    discriminant23_characterFold_one_sub
  intro w hw hy
  apply character_ne_zero_of_right_or_reflected hw.1 hw.2
  · by_cases h : (1 / 2 : ℝ) ≤ w.re
    · exact .inl h
    · exact .inr (by linarith only [lt_of_not_ge h])
  · intro z ha hb hz
    exact hRight z ⟨ha, hb⟩ (hz ▸ hy)

theorem discriminant23_strip_increment_of_right_crossing {a b d : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hA : 0 < d * (discriminant23CharacterFold ⟨1 / 2, a⟩).re)
    (hB : d * (discriminant23CharacterFold ⟨1 / 2, b⟩).re < 0)
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (1 / 2 : ℝ) (5 / 8) → w.im ∈ Icc a b →
      0 < d * (deriv discriminant23CharacterFold w).im)
    (hExterior : ∀ w : ℂ, w.re ∈ Icc (5 / 8 : ℝ) (7 / 8) → w.im ∈ Icc a b →
      discriminant23CharacterFold w ≠ 0) :
    discriminant23CharacterCountingFunction.HasStripZeroIncrement a b 1 := by
  apply discriminant23CharacterCountingFunction.hasStripZeroIncrement_of_signed_crossing
    (l := 3 / 8) (r := 5 / 8) ha hab (by constructor <;> norm_num) discriminant23_characterFold_one_sub
    (fun t _ ↦ discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl) hA hB
  · intro w hx hy
    change 0 < d * (deriv discriminant23CharacterFold w).im
    by_cases hr : (1 / 2 : ℝ) ≤ w.re
    · exact hSlope w ⟨hr, hx.2⟩ hy
    · have hz : (1 - conj w).re ∈ Icc (1 / 2 : ℝ) (5 / 8) := by
        rw [reflected_re]
        exact ⟨by linarith only [lt_of_not_ge hr], by linarith only [hx.1]⟩
      have hs := hSlope (1 - conj w) hz ((reflected_im w) ▸ hy)
      simpa only [discriminant23_characterFold_deriv_im_same_height_reflection] using hs
  · intro w hx hy hz
    constructor
    · by_contra! hl
      exact character_ne_zero_of_right_or_reflected hx.1 hx.2
        (.inr (show (5 / 8 : ℝ) ≤ 1 - w.re by linarith only [hl]))
        (fun z hlow hhigh hi ↦ hExterior z ⟨hlow, hhigh⟩ (hi ▸ hy)) hz
    · by_contra! hh
      exact character_ne_zero_of_right_or_reflected hx.1 hx.2 (.inl hh.le)
        (fun z hlow hhigh hi ↦ hExterior z ⟨hlow, hhigh⟩ (hi ▸ hy)) hz

#print axioms discriminant23_strip_increment_of_right_nonvanishing
#print axioms discriminant23_strip_increment_of_right_crossing

end FieldTarget
