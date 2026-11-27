import DedekindDiscriminant23ReadingIntervals
import MellinFixedComplexPolynomial

/-! Evaluate the two discriminant-23 polynomials on rational rectangles.
The center lies on the imaginary axis in the normalized coordinate. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed
open scoped BigOperators

noncomputable section

private def imaginaryCenter (m d : ℤ) : ℂ :=
  (((m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I

/-- The magnitude factor of a center power is one rational. Its phase is
determined by the exponent modulo four. -/
def imaginaryCenterPowerBox (m d : ℤ) (k : ℕ) : ComplexBox :=
  let a := fromRatio (m ^ k) (d ^ k)
  match k % 4 with
  | 0 => ComplexBox.real a
  | 1 => ⟨constant 0, a⟩
  | 2 => ComplexBox.real (neg a)
  | _ => ⟨constant 0, neg a⟩

private theorem I_power_mod (k : ℕ) : Complex.I ^ k = Complex.I ^ (k % 4) := by
  have h₄ : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]
    norm_num
  calc
    _ = Complex.I ^ (k % 4 + 4 * (k / 4)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, h₄, one_pow, mul_one]

theorem imaginaryCenterPowerBox_contains {m d : ℤ} (hd : 0 < d) (k : ℕ) :
    ComplexBox.Contains (imaginaryCenterPowerBox m d k) (imaginaryCenter m d ^ k) := by
  let x := (m : ℝ) / (d : ℝ)
  have hx : Contains (fromRatio (m ^ k) (d ^ k)) (x ^ k) := by
    simpa only [x, Int.cast_pow, div_pow] using ratio_contains (m ^ k) (pow_pos hd k)
  have hneg := neg_contains hx
  have hzero := constant_contains 0
  have h₃ : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_add, Complex.I_sq, pow_one, neg_one_mul]
  rw [imaginaryCenter, mul_pow, ← Complex.ofReal_pow, I_power_mod]
  change ComplexBox.Contains (imaginaryCenterPowerBox m d k) ((x ^ k : ℝ) * Complex.I ^ (k % 4))
  have hmod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · simpa only [imaginaryCenterPowerBox, h, pow_zero, mul_one] using ComplexBox.real_contains hx
  · refine ⟨?_, ?_⟩
    · simpa only [imaginaryCenterPowerBox, h, pow_one, Complex.mul_I_re, Complex.ofReal_im,
        neg_zero, Int.cast_zero] using hzero
    · simpa only [imaginaryCenterPowerBox, h, pow_one, Complex.mul_I_im, Complex.ofReal_re] using hx
  · simpa only [imaginaryCenterPowerBox, h, Complex.I_sq, mul_neg, mul_one, ← Complex.ofReal_neg] using
      ComplexBox.real_contains hneg
  · rw [h, h₃]
    refine ⟨?_, ?_⟩
    · simpa only [imaginaryCenterPowerBox, h, mul_neg, Complex.neg_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, Int.cast_zero] using hzero
    · simpa only [imaginaryCenterPowerBox, h, mul_neg, Complex.neg_im, Complex.mul_I_im,
        Complex.ofReal_re] using hneg

/-- Keep the first 34 Taylor terms in the rectangle calculation. -/
def discriminant23ReadingTerms : ℕ := 34

def discriminant23ReadingTaylorUpTo (odd : Bool) (terms : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range terms, (discriminant23ReadingCoefficient odd k : ℂ) *
    discriminant23ReadingArgument w ^ k

def discriminant23ReadingPartialTaylor (odd : Bool) (w : ℂ) : ℂ :=
  discriminant23ReadingTaylorUpTo odd discriminant23ReadingTerms w

/-- The imaginary endpoints are centered offsets. The real endpoints are in
units of the supplied horizontal denominator. -/
def discriminant23ReadingCellBoxUpTo (coefficient : ℕ → Box) (terms : ℕ)
    (m radius d left right dx : ℤ) : ComplexBox :=
  let argument : ComplexBox := ⟨rangeRatio left right dx, rangeRatio (-radius) radius d⟩
  ComplexBox.horner argument (ComplexBox.shiftedCoefficient
    (fun j ↦ ComplexBox.real (coefficient j)) (imaginaryCenterPowerBox m d) terms) 0 terms

def discriminant23ReadingCellBox (coefficient : ℕ → Box)
    (m radius d left right : ℤ) : ComplexBox :=
  discriminant23ReadingCellBoxUpTo coefficient discriminant23ReadingTerms m radius d left right 12

theorem discriminant23_readingCellBoxUpTo_contains
    (coefficient : ℕ → Box) (odd : Bool) (terms : ℕ)
    (hCoeff : ∀ k, Contains (coefficient k) (discriminant23ReadingCoefficient odd k))
    {m radius d left right dx : ℤ} (hd : 0 < d) (hx : 0 < dx) {w : ℂ}
    (hRe₀ : (left : ℝ) / (dx : ℝ) ≤ (discriminant23ReadingArgument w).re)
    (hRe₁ : (discriminant23ReadingArgument w).re ≤ (right : ℝ) / (dx : ℝ))
    (hIm₀ : (-(radius : ℝ)) / (d : ℝ) ≤ (discriminant23ReadingArgument w).im - (m : ℝ) / (d : ℝ))
    (hIm₁ : (discriminant23ReadingArgument w).im - (m : ℝ) / (d : ℝ) ≤ (radius : ℝ) / (d : ℝ)) :
    ComplexBox.Contains (discriminant23ReadingCellBoxUpTo coefficient terms m radius d left right dx)
      (discriminant23ReadingTaylorUpTo odd terms w) := by
  let c := imaginaryCenter m d
  let z := discriminant23ReadingArgument w - c
  have hZre : z.re = (discriminant23ReadingArgument w).re := by
    simp [z, c, imaginaryCenter, Complex.sub_re]
  have hZim : z.im = (discriminant23ReadingArgument w).im - (m : ℝ) / (d : ℝ) := by
    simp [z, c, imaginaryCenter, Complex.sub_im]
  have hz : ComplexBox.Contains ⟨rangeRatio left right dx, rangeRatio (-radius) radius d⟩ z := by
    constructor
    · rw [hZre]
      exact rangeRatio_contains hx hRe₀ hRe₁
    · rw [hZim]
      exact rangeRatio_contains hd (by simpa only [Int.cast_neg] using hIm₀) hIm₁
  have hs := ComplexBox.shifted_horner_contains hz
    (fun j ↦ ComplexBox.real (coefficient j)) (imaginaryCenterPowerBox m d)
    (fun j ↦ (discriminant23ReadingCoefficient odd j : ℂ)) c
    (fun j ↦ ComplexBox.real_contains (hCoeff j)) (imaginaryCenterPowerBox_contains hd)
    terms
  have hTotal : c + z = discriminant23ReadingArgument w := by dsimp [z]; ring
  rw [hTotal] at hs
  exact hs

theorem discriminant23_readingCellBox_contains
    (coefficient : ℕ → Box) (odd : Bool)
    (hCoeff : ∀ k, Contains (coefficient k) (discriminant23ReadingCoefficient odd k))
    {m radius d left right : ℤ} (hd : 0 < d) {w : ℂ}
    (hRe₀ : (left : ℝ) / 12 ≤ (discriminant23ReadingArgument w).re)
    (hRe₁ : (discriminant23ReadingArgument w).re ≤ (right : ℝ) / 12)
    (hIm₀ : (-(radius : ℝ)) / (d : ℝ) ≤ (discriminant23ReadingArgument w).im - (m : ℝ) / (d : ℝ))
    (hIm₁ : (discriminant23ReadingArgument w).im - (m : ℝ) / (d : ℝ) ≤ (radius : ℝ) / (d : ℝ)) :
    ComplexBox.Contains (discriminant23ReadingCellBox coefficient m radius d left right)
      (discriminant23ReadingPartialTaylor odd w) :=
  discriminant23_readingCellBoxUpTo_contains coefficient odd discriminant23ReadingTerms hCoeff
    hd (dx := 12) (by norm_num) hRe₀ hRe₁ hIm₀ hIm₁

def discriminant23BelowBox (coefficient : ℕ → Box) (j : Fin 16) : ComplexBox :=
  discriminant23ReadingCellBox coefficient (61 + 10 * (j.val : ℤ)) 5 288 (-1) 1

def discriminant23SlopeBox (coefficient : ℕ → Box) (j : Fin 14) : ComplexBox :=
  discriminant23ReadingCellBox coefficient (2027 + 22 * (j.val : ℤ)) 11 2688 (-1) 1

def discriminant23AboveBox (coefficient : ℕ → Box) (rightSide : Bool) (j : Fin 8) : ComplexBox :=
  discriminant23ReadingCellBox coefficient (1333 + 10 * (j.val : ℤ)) 5 1536
    (if rightSide then 0 else -1) (if rightSide then 1 else 0)

/-- Leave room for the omitted coefficient mass as well as the full-model sign margin. -/
def discriminant23ReadingMargin : ℤ :=
  83 * 10 ^ 18

#print axioms imaginaryCenterPowerBox_contains
#print axioms discriminant23_readingCellBoxUpTo_contains
#print axioms discriminant23_readingCellBox_contains

end

end FieldTarget

