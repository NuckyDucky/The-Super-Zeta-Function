import DedekindDiscriminant23GaussCentered
import Gauss23ReducedPhase
import Gauss23AmplitudeCache

/-! Directed intervals for the centered quadrature coefficients and their signs on boxes. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

private def scaledPower (x : Box) : ℕ → Box
  | 0 => constant 1
  | k + 1 => divInt (mul (scaledPower x k) x) (k + 1 : ℕ)

private theorem scaledPower_contains {x : Box} {u : ℝ} (hx : Contains x u) (k : ℕ) :
    Contains (scaledPower x k) (u ^ k / (k.factorial : ℝ)) := by
  induction k with
  | zero => simpa [scaledPower] using constant_contains 1
  | succ k ih =>
    have hd : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by positivity
    rw [scaledPower]
    convert divInt_contains (mul_contains ih hx) hd using 1
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hs : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hf, hs]

private def coefficientSampleBox (slope : Bool) (m d : ℤ) (k : ℕ) (j : Fin 16) (i : Fin 24) :
    ComplexBox :=
  let node := gauss23NodeBox j i
  let amp := gauss23CachedAmplitudeBox j i
  let phase := cosSinFixed (gauss23CriticalPhaseBox m d j i)
  let weight := if slope then mul node amp else amp
  let plus := ComplexBox.mul (ComplexBox.real weight) ⟨phase.1, phase.2⟩
  let minus := ComplexBox.mul (ComplexBox.real (if slope then neg weight else weight))
    ⟨phase.1, neg phase.2⟩
  ComplexBox.mul (ComplexBox.add plus (ComplexBox.intMul ((-1 : ℤ) ^ k) minus))
    (ComplexBox.real (scaledPower node k))

private theorem coefficientSampleBox_contains (slope : Bool) (m : ℤ) {d : ℤ} (hd : 0 < d)
    (hT : |(m : ℝ) / d| ≤ 20) (k : ℕ) {j : ℕ} (i : Fin 24) :
    ComplexBox.Contains (coefficientSampleBox slope m d k (Fin.ofNat 16 j) i)
      ((gauss23CenteredPlus slope ((m : ℝ) / d) (j, i) +
          (-1 : ℂ) ^ k * gauss23CenteredMinus slope ((m : ℝ) / d) (j, i)) *
        (gauss23CenteredNode (j, i) : ℂ) ^ k / (k.factorial : ℂ)) := by
  let j' := Fin.ofNat 16 j
  let u := gauss23LogNode j' i
  let a := gauss23Amplitude j' i
  let theta := ((m : ℝ) / d) * u
  let node := gauss23NodeBox j' i
  let amp := gauss23CachedAmplitudeBox j' i
  let phase := cosSinFixed (gauss23CriticalPhaseBox m d j' i)
  let weight := if slope then mul node amp else amp
  have hn : Contains node u := gauss23_nodeBox_contains j' i
  have ha : Contains amp a := by
    dsimp only [amp]
    rw [gauss23_cachedAmplitudeBox_eq]
    exact gauss23_amplitudeBox_contains j' i
  have hPhase := cosSinFixed_contains (gauss23_phaseBox_contains m hd j' i)
    (gauss23_phaseCheck_of_height m hd hT j' i)
  have hp : ComplexBox.Contains ⟨phase.1, phase.2⟩ (Complex.exp ((theta : ℂ) * Complex.I)) := by
    constructor
    · rw [Complex.exp_ofReal_mul_I_re]
      exact hPhase.1
    · rw [Complex.exp_ofReal_mul_I_im]
      exact hPhase.2
  have hm : ComplexBox.Contains ⟨phase.1, neg phase.2⟩ (Complex.exp (-((theta : ℂ) * Complex.I))) := by
    have harg : -((theta : ℂ) * Complex.I) = ((-theta : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    constructor
    · rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      exact hPhase.1
    · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      exact neg_contains hPhase.2
  have hw : Contains weight ((if slope then u else 1) * a) := by
    cases slope
    · simpa only [weight, Bool.false_eq_true, ↓reduceIte, one_mul] using ha
    · exact mul_contains hn ha
  have hwm : Contains (if slope then neg weight else weight) ((if slope then -u else 1) * a) := by
    cases slope
    · exact hw
    · simpa only [↓reduceIte, neg_mul] using neg_contains hw
  have hPlus := ComplexBox.mul_contains (ComplexBox.real_contains hw) hp
  have hMinus := ComplexBox.mul_contains (ComplexBox.real_contains hwm) hm
  have h := ComplexBox.mul_contains
    (ComplexBox.add_contains hPlus (ComplexBox.intMul_contains ((-1 : ℤ) ^ k) hMinus))
    (ComplexBox.real_contains (scaledPower_contains hn k))
  convert h using 1
  · rfl
  · unfold gauss23CenteredPlus gauss23CenteredMinus gauss23CenteredNode gauss23CenteredAmplitude
    dsimp only [j', theta, u, a]
    push_cast
    ring

def gauss23CoefficientBox (slope : Bool) (m d : ℤ) (k : ℕ) : ComplexBox :=
  ComplexBox.sumRange (fun j ↦ ComplexBox.sumRange
    (fun i ↦ coefficientSampleBox slope m d k (Fin.ofNat 16 j) (Fin.ofNat 24 i)) 24) 16

theorem gauss23_coefficientBox_contains (slope : Bool) (m : ℤ) {d : ℤ}
    (hd : 0 < d) (hT : |(m : ℝ) / d| ≤ 20) (k : ℕ) :
    ComplexBox.Contains (gauss23CoefficientBox slope m d k) (gauss23CenteredCoeff slope ((m : ℝ) / d) k) := by
  unfold gauss23CoefficientBox gauss23CenteredCoeff centeredExponentialSumCoeff gauss23CenteredNodes
  rw [Finset.sum_product]
  apply ComplexBox.sumRange_contains
  intro j _
  let f (i : Fin 24) :=
    (gauss23CenteredPlus slope ((m : ℝ) / d) (j, i) +
      (-1 : ℂ) ^ k * gauss23CenteredMinus slope ((m : ℝ) / d) (j, i)) *
        (gauss23CenteredNode (j, i) : ℂ) ^ k / (k.factorial : ℂ)
  change ComplexBox.Contains _ (∑ i : Fin 24, f i)
  have hsum : (∑ i : Fin 24, f i) = ∑ n ∈ Finset.range 24, f (Fin.ofNat 24 n) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n ↦ f (Fin.ofNat 24 n))]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Fin.ofNat 24 i.val = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
  rw [hsum]
  exact ComplexBox.sumRange_contains _ _ (fun i _ ↦
    coefficientSampleBox_contains slope m hd hT k (Fin.ofNat 24 i))

def gauss23CellBox (slope : Bool) (m d : ℤ) (offset : ComplexBox) : ComplexBox :=
  ComplexBox.horner offset (gauss23CoefficientBox slope m d) 0 36

theorem gauss23_cellBox_contains (slope : Bool) (m : ℤ) {d : ℤ} (hd : 0 < d)
    (hT : |(m : ℝ) / d| ≤ 20) {offset : ComplexBox} {w : ℂ}
    (hw : ComplexBox.Contains offset (w - gauss23CriticalPoint ((m : ℝ) / d))) :
    ComplexBox.Contains (gauss23CellBox slope m d offset) (gauss23CenteredTaylor slope ((m : ℝ) / d) 36 w) := by
  simpa only [gauss23CellBox, gauss23CenteredTaylor, Nat.zero_add] using
    ComplexBox.horner_contains hw (gauss23CoefficientBox slope m d)
      (gauss23CenteredCoeff slope ((m : ℝ) / d)) (gauss23_coefficientBox_contains slope m hd hT) 0 36

private def boxPowers (a : ComplexBox) : ℕ → ComplexBox
  | 0 => ComplexBox.real (constant 1)
  | k + 1 => ComplexBox.mul (boxPowers a k) a

private theorem boxPowers_contains {a : ComplexBox} {z : ℂ}
    (h : ComplexBox.Contains a z) (k : ℕ) : ComplexBox.Contains (boxPowers a k) (z ^ k) := by
  induction k with
  | zero =>
    simpa [boxPowers] using ComplexBox.real_contains (constant_contains 1)
  | succ k ih =>
    rw [boxPowers, pow_succ]
    exact ComplexBox.mul_contains ih h

/-- Recenter the same polynomial inside a cell using only its existing coefficients. -/
def gauss23ShiftedCellBox (slope : Bool) (m d : ℤ) (center offset : ComplexBox) : ComplexBox :=
  ComplexBox.horner offset
    (ComplexBox.shiftedCoefficient (gauss23CoefficientBox slope m d) (boxPowers center) 36) 0 36

theorem gauss23_shiftedCellBox_contains (slope : Bool) (m : ℤ) {d : ℤ} (hd : 0 < d)
    (hT : |(m : ℝ) / d| ≤ 20) {center offset : ComplexBox} {z w : ℂ}
    (hz : ComplexBox.Contains center z)
    (hw : ComplexBox.Contains offset (w - gauss23CriticalPoint ((m : ℝ) / d) - z)) :
    ComplexBox.Contains (gauss23ShiftedCellBox slope m d center offset)
      (gauss23CenteredTaylor slope ((m : ℝ) / d) 36 w) := by
  have h := ComplexBox.shifted_horner_contains hw (gauss23CoefficientBox slope m d)
    (boxPowers center) (gauss23CenteredCoeff slope ((m : ℝ) / d)) z
    (gauss23_coefficientBox_contains slope m hd hT) (boxPowers_contains hz) 36
  have he : z + (w - gauss23CriticalPoint ((m : ℝ) / d) - z) =
      w - gauss23CriticalPoint ((m : ℝ) / d) := by abel
  simpa only [gauss23ShiftedCellBox, gauss23CenteredTaylor, he] using h

#print axioms gauss23_coefficientBox_contains
#print axioms gauss23_cellBox_contains
#print axioms gauss23_shiftedCellBox_contains

end FieldTarget
