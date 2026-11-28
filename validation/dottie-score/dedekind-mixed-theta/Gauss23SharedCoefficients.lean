import Gauss23CoefficientIntervals

/-! Share each real trigonometric enclosure across the Taylor coefficients.
The derivative reuses the next coefficient of the value polynomial. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

def gauss23UnitPhaseBox (j : Fin 16) (i : Fin 24) : ComplexBox :=
  let phase := cosSinFixed (gauss23CriticalPhaseBox 1 1 j i)
  ⟨phase.1, phase.2⟩

theorem gauss23_unitPhaseBox_contains (j : Fin 16) (i : Fin 24) :
    ComplexBox.Contains (gauss23UnitPhaseBox j i)
      (Complex.exp ((gauss23LogNode j i : ℂ) * Complex.I)) := by
  have hPhase := cosSinFixed_contains (gauss23_phaseBox_contains 1 (d := 1) (by decide) j i)
    (gauss23_phaseCheck_of_height 1 (d := 1) (by decide) (by norm_num) j i)
  constructor
  · rw [Complex.exp_ofReal_mul_I_re]
    simpa only [gauss23UnitPhaseBox, Int.cast_one, div_one, one_mul] using hPhase.1
  · rw [Complex.exp_ofReal_mul_I_im]
    simpa only [gauss23UnitPhaseBox, Int.cast_one, div_one, one_mul] using hPhase.2

def gauss23BoxPower (a : ComplexBox) : ℕ → ComplexBox
  | 0 => ComplexBox.real (constant 1)
  | k + 1 => ComplexBox.mul (gauss23BoxPower a k) a

theorem gauss23_boxPower_contains {a : ComplexBox} {z : ℂ}
    (h : ComplexBox.Contains a z) (k : ℕ) :
    ComplexBox.Contains (gauss23BoxPower a k) (z ^ k) := by
  induction k with
  | zero => simpa [gauss23BoxPower] using ComplexBox.real_contains (constant_contains 1)
  | succ k ih =>
    rw [gauss23BoxPower, pow_succ]
    exact ComplexBox.mul_contains ih h

def gauss23IntegerWeightBox (phase : ComplexBox) (m : ℕ) (j : Fin 16) (i : Fin 24) : Box × Box :=
  let amplitude := mul (constant 2) (gauss23CachedAmplitudeBox j i)
  let p := gauss23BoxPower phase m
  (mul amplitude p.re, mul amplitude p.im)

def Gauss23WeightContains (t : ℝ) (p : Box × Box) (j : Fin 16) (i : Fin 24) : Prop :=
  let a := 2 * gauss23Amplitude j i
  let θ := t * gauss23LogNode j i
  Contains p.1 (a * Real.cos θ) ∧ Contains p.2 (a * Real.sin θ)

theorem gauss23_integerWeightBox_contains (m : ℕ) (j : Fin 16) (i : Fin 24)
    {phase : ComplexBox} (h : ComplexBox.Contains phase
      (Complex.exp ((gauss23LogNode j i : ℂ) * Complex.I))) :
    Gauss23WeightContains (m : ℝ) (gauss23IntegerWeightBox phase m j i) j i := by
  have ha : Contains (gauss23CachedAmplitudeBox j i) (gauss23Amplitude j i) := by
    rw [gauss23_cachedAmplitudeBox_eq]
    exact gauss23_amplitudeBox_contains j i
  have ha₂ := mul_contains (constant_contains 2) ha
  have hPhase := gauss23_boxPower_contains h m
  rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hPhase
  have hRe := hPhase.1
  have hIm := hPhase.2
  rw [Complex.exp_ofReal_mul_I_re] at hRe
  rw [Complex.exp_ofReal_mul_I_im] at hIm
  exact ⟨mul_contains ha₂ hRe, mul_contains ha₂ hIm⟩

private def exactScaledNodePower (j : Fin 16) (i : Fin 24) (k : ℕ) : Box :=
  fromRatio (gauss23NodeNumerator j i ^ k) (gauss23NodeDenominator ^ k * (k.factorial : ℤ))

private theorem exactScaledNodePower_contains (j : Fin 16) (i : Fin 24) (k : ℕ) :
    Contains (exactScaledNodePower j i k) (gauss23LogNode j i ^ k / (k.factorial : ℝ)) := by
  have hD : 0 < gauss23NodeDenominator := by norm_num [gauss23NodeDenominator, gauss24Denominator]
  have hF : (0 : ℤ) < (k.factorial : ℤ) := by positivity
  have h := ratio_contains (gauss23NodeNumerator j i ^ k) (mul_pos (pow_pos hD k) hF)
  dsimp only [exactScaledNodePower, gauss23LogNode]
  push_cast at h
  simpa only [div_pow, div_div] using h

private theorem neg_one_pow_parity (k : ℕ) :
    (-1 : ℂ) ^ k = if k % 2 = 0 then 1 else -1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    by_cases hk : k % 2 = 0
    · have hs : (k + 1) % 2 ≠ 0 := by omega
      simp [hk, hs]
    · have hs : (k + 1) % 2 = 0 := by omega
      simp [hk, hs]

private theorem gauss23_value_phase (t : ℝ) (p : ℕ × Fin 24) (k : ℕ) :
    gauss23CenteredPlus false t p + (-1 : ℂ) ^ k * gauss23CenteredMinus false t p =
      if k % 2 = 0 then
        ((2 * gauss23CenteredAmplitude p * Real.cos (t * gauss23CenteredNode p) : ℝ) : ℂ)
      else
        ((2 * gauss23CenteredAmplitude p * Real.sin (t * gauss23CenteredNode p) : ℝ) : ℂ) * Complex.I := by
  let a := gauss23CenteredAmplitude p
  let θ := t * gauss23CenteredNode p
  rw [neg_one_pow_parity]
  simp only [gauss23CenteredPlus, gauss23CenteredMinus, Bool.false_eq_true, ↓reduceIte, one_mul]
  change (↑a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
      (if k % 2 = 0 then 1 else -1) * (↑a * Complex.exp (-((θ : ℂ) * Complex.I))) =
      (if k % 2 = 0 then ((2 * a * Real.cos θ : ℝ) : ℂ)
        else ((2 * a * Real.sin θ : ℝ) : ℂ) * Complex.I)
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  by_cases hk : k % 2 = 0
  · simp only [ite_eq_left hk, one_mul]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
        Real.cos_neg, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
        Real.sin_neg, Complex.ofReal_im]
      ring
  · simp only [ite_eq_right hk, neg_one_mul]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
        Real.cos_neg, Complex.I_re, mul_zero]
      ring
    · simp only [Complex.add_im, Complex.neg_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
        Real.sin_neg, Complex.I_im, mul_one]
      ring

private theorem gauss23_slope_coefficient (t : ℝ) (k : ℕ) :
    gauss23CenteredCoeff true t k = ((k + 1 : ℕ) : ℂ) * gauss23CenteredCoeff false t (k + 1) := by
  unfold gauss23CenteredCoeff centeredExponentialSumCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hp : gauss23CenteredPlus true t p =
      (gauss23CenteredNode p : ℂ) * gauss23CenteredPlus false t p := by
    unfold gauss23CenteredPlus
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Complex.ofReal_mul]
    ring
  have hm : gauss23CenteredMinus true t p =
      -(gauss23CenteredNode p : ℂ) * gauss23CenteredMinus false t p := by
    unfold gauss23CenteredMinus
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [hp, hm, Nat.factorial_succ, pow_succ (-1 : ℂ), pow_succ (gauss23CenteredNode p : ℂ)]
  push_cast
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hs : (↑k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk, hs]

private def valueSampleBox (p : Box × Box) (j : Fin 16) (i : Fin 24) (k : ℕ) : ComplexBox :=
  let power := exactScaledNodePower j i k
  if k % 2 = 0 then ComplexBox.real (mul p.1 power)
  else ⟨constant 0, mul p.2 power⟩

private theorem valueSampleBox_contains (t : ℝ) (k j : ℕ) (i : Fin 24)
    {weights : Box × Box} (hw : Gauss23WeightContains t weights (Fin.ofNat 16 j) i) :
    let p := (j, i)
    ComplexBox.Contains (valueSampleBox weights (Fin.ofNat 16 j) i k)
      ((gauss23CenteredPlus false t p + (-1 : ℂ) ^ k * gauss23CenteredMinus false t p) *
        (gauss23CenteredNode p : ℂ) ^ k / (k.factorial : ℂ)) := by
  dsimp only
  rw [gauss23_value_phase]
  have hp := exactScaledNodePower_contains (Fin.ofNat 16 j) i k
  unfold valueSampleBox
  split_ifs with hk
  · convert ComplexBox.real_contains (mul_contains hw.1 hp) using 1
    simp only [gauss23CenteredAmplitude, gauss23CenteredNode]
    push_cast
    ring
  · have h := mul_contains hw.2 hp
    have he :
        ((2 * gauss23CenteredAmplitude (j, i) *
            Real.sin (t * gauss23CenteredNode (j, i)) : ℝ) : ℂ) * Complex.I *
            (gauss23CenteredNode (j, i) : ℂ) ^ k / (k.factorial : ℂ) =
          ((2 * gauss23Amplitude (Fin.ofNat 16 j) i *
            Real.sin (t * gauss23LogNode (Fin.ofNat 16 j) i) *
            (gauss23LogNode (Fin.ofNat 16 j) i ^ k / (k.factorial : ℝ)) : ℝ) : ℂ) * Complex.I := by
      simp only [gauss23CenteredAmplitude, gauss23CenteredNode]
      push_cast
      ring
    rw [he]
    constructor
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, Int.cast_zero] using constant_contains 0
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, zero_mul, add_zero] using h

def gauss23SharedValueCoefficient (weights : Fin 16 → Fin 24 → Box × Box) (k : ℕ) : ComplexBox :=
  ComplexBox.sumRange (fun j ↦ ComplexBox.sumRange (fun i ↦
    let j' := Fin.ofNat 16 j
    let i' := Fin.ofNat 24 i
    valueSampleBox (weights j' i') j' i' k) 24) 16

theorem gauss23_sharedValueCoefficient_contains (weights : Fin 16 → Fin 24 → Box × Box)
    (t : ℝ) (hWeights : ∀ j i, Gauss23WeightContains t (weights j i) j i) (k : ℕ) :
    ComplexBox.Contains (gauss23SharedValueCoefficient weights k)
      (gauss23CenteredCoeff false t k) := by
  unfold gauss23SharedValueCoefficient gauss23CenteredCoeff centeredExponentialSumCoeff gauss23CenteredNodes
  rw [Finset.sum_product]
  apply ComplexBox.sumRange_contains
  intro j _
  let f (i : Fin 24) :=
    (gauss23CenteredPlus false t (j, i) +
      (-1 : ℂ) ^ k * gauss23CenteredMinus false t (j, i)) *
      (gauss23CenteredNode (j, i) : ℂ) ^ k / (k.factorial : ℂ)
  change ComplexBox.Contains _ (∑ i : Fin 24, f i)
  have hsum : (∑ i : Fin 24, f i) = ∑ n ∈ Finset.range 24, f (Fin.ofNat 24 n) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n ↦ f (Fin.ofNat 24 n))]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Fin.ofNat 24 i.val = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
  rw [hsum]
  apply ComplexBox.sumRange_contains
  intro i _
  exact valueSampleBox_contains t k j (Fin.ofNat 24 i) (hWeights _ _)

def gauss23SharedCoefficient (value : ℕ → ComplexBox) (slope : Bool) (k : ℕ) : ComplexBox :=
  if slope then ComplexBox.intMul ((k + 1 : ℕ) : ℤ) (value (k + 1)) else value k

theorem gauss23_sharedCoefficient_contains (value : ℕ → ComplexBox) (t : ℝ)
    (hValue : ∀ k ≤ 36, ComplexBox.Contains (value k) (gauss23CenteredCoeff false t k))
    (slope : Bool) {k : ℕ} (hk : k < 36) :
    ComplexBox.Contains (gauss23SharedCoefficient value slope k) (gauss23CenteredCoeff slope t k) := by
  cases slope
  · exact hValue k (by omega)
  · rw [gauss23_slope_coefficient]
    simpa only [gauss23SharedCoefficient, ↓reduceIte, Int.cast_natCast] using
      ComplexBox.intMul_contains ((k + 1 : ℕ) : ℤ) (hValue (k + 1) (by omega))

#print axioms gauss23_unitPhaseBox_contains
#print axioms gauss23_integerWeightBox_contains
#print axioms gauss23_sharedValueCoefficient_contains
#print axioms gauss23_sharedCoefficient_contains

end FieldTarget
