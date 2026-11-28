import DedekindDiscriminant23GaussQuadrature
import DedekindDiscriminant23GaussIntervals
import MellinFixedComplexPolynomial

/-! Exact interval evaluation of the quadrature on the critical line. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

def gauss23CriticalPoint (t : ℝ) : ℂ := ⟨1 / 2, t⟩

private theorem gaussIntegrand_critical_re (t u : ℝ) :
    (discriminant23GaussIntegrand false (gauss23CriticalPoint t) (u : ℂ)).re =
      2 * Real.exp (u / 2) * Real.cos (t * u) *
        discriminant23CharacterPolynomialUpTo 64 (Real.exp (-discriminant23ThetaScale * Real.exp u)) := by
  rw [discriminant23_gaussIntegrand_real_eq]
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_re, Complex.mul_im,
    zero_add, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, gauss23CriticalPoint]
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
    show (1 / 2 : ℝ) * u = u / 2 by ring, zero_sub, neg_mul, Real.cos_neg]
  ring

def gauss23CriticalSample (t : ℝ) (j : Fin 16) (i : Fin 24) : ℝ :=
  (2 * gauss23Amplitude j i) * Real.cos (t * gauss23LogNode j i)

def gauss23CriticalFiniteSum (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 16, ∑ i ∈ Finset.range 24, gauss23CriticalSample t (Fin.ofNat 16 j) (Fin.ofNat 24 i)

theorem gauss23_criticalReading_eq_sum (t : ℝ) :
    (discriminant23GaussReading false (gauss23CriticalPoint t)).re = gauss23CriticalFiniteSum t := by
  unfold discriminant23GaussReading rationalCompositeRule rationalPanelRule gauss23CriticalFiniteSum
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (Fin.ofNat 16 j).val = j := Nat.mod_eq_of_lt (Finset.mem_range.mp hj)
  have hn (i : Fin 24) :
      (0 : ℝ) + (2 * (j : ℝ) + 1) * (1 / 8) + (1 / 8) * (gauss24Node i : ℝ) =
        gauss23LogNode (Fin.ofNat 16 j) i := by rw [gauss23_node_eq, hj']; ring
  simp_rw [hn, ← Complex.ofReal_ratCast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_sum, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ gauss23CriticalSample t (Fin.ofNat 16 j) (Fin.ofNat 24 i))]
  apply Finset.sum_congr rfl
  intro i _
  have hidx : (Fin.ofNat 24 i.val : Fin 24) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hidx]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gaussIntegrand_critical_re]
  unfold gauss23CriticalSample gauss23Amplitude gauss23LogWeight
  ring

def gauss23CriticalPhaseBox (m d : ℤ) (j : Fin 16) (i : Fin 24) : Box :=
  fromRatio (m * gauss23NodeNumerator j i) (d * gauss23NodeDenominator)

theorem gauss23_phaseBox_contains (m : ℤ) {d : ℤ} (hd : 0 < d) (j : Fin 16) (i : Fin 24) :
    Contains (gauss23CriticalPhaseBox m d j i) (((m : ℝ) / d) * gauss23LogNode j i) := by
  have hp : 0 < d * gauss23NodeDenominator := mul_pos hd (by norm_num [gauss23NodeDenominator, gauss24Denominator])
  simpa only [gauss23CriticalPhaseBox, gauss23LogNode, Int.cast_mul, div_mul_div_comm] using
    ratio_contains (m * gauss23NodeNumerator j i) hp

def gauss23PhaseCheck (m d : ℤ) (j : Fin 16) (i : Fin 24) : Bool :=
  inUnit (divInt (reducedPhase (gauss23CriticalPhaseBox m d j i)) 4)

def gauss23CriticalSampleBox (m d : ℤ) (j : Fin 16) (i : Fin 24) : Box :=
  mul (mul (constant 2) (gauss23AmplitudeBox j i)) (cosSinFixed (gauss23CriticalPhaseBox m d j i)).1

theorem gauss23_sampleBox_contains (m : ℤ) {d : ℤ} (hd : 0 < d) (j : Fin 16) (i : Fin 24)
    (hphase : gauss23PhaseCheck m d j i = true) :
    Contains (gauss23CriticalSampleBox m d j i) (gauss23CriticalSample ((m : ℝ) / d) j i) := by
  have hCos := (cosSinFixed_contains (gauss23_phaseBox_contains m hd j i) hphase).1
  simpa only [gauss23CriticalSampleBox, gauss23CriticalSample, Int.cast_ofNat] using
    mul_contains (mul_contains (constant_contains 2) (gauss23_amplitudeBox_contains j i)) hCos

private def sumBoxes (f : ℕ → Box) : ℕ → Box
  | 0 => constant 0
  | k + 1 => add (sumBoxes f k) (f k)

private theorem sumBoxes_contains (f : ℕ → Box) (g : ℕ → ℝ) {n : ℕ}
    (h : ∀ k < n, Contains (f k) (g k)) : Contains (sumBoxes f n) (∑ k ∈ Finset.range n, g k) := by
  induction n with
  | zero => simpa [sumBoxes] using constant_contains 0
  | succ k ih =>
    rw [sumBoxes, Finset.sum_range_succ]
    exact add_contains (ih (fun j hj ↦ h j (Nat.lt_succ_of_lt hj))) (h k (Nat.lt_succ_self k))

def gauss23CriticalPanelBox (m d : ℤ) (j : ℕ) : Box :=
  sumBoxes (fun i ↦ gauss23CriticalSampleBox m d (Fin.ofNat 16 j) (Fin.ofNat 24 i)) 24

def gauss23CriticalValueBox (m d : ℤ) : Box :=
  sumBoxes (gauss23CriticalPanelBox m d) 16

private theorem sumBoxes_eq_sums (f : ℕ → Box) (n : ℕ) : sumBoxes f n =
    ⟨∑ j ∈ Finset.range n, (f j).lo, ∑ j ∈ Finset.range n, (f j).hi⟩ := by
  induction n with
  | zero => simp [sumBoxes, constant]
  | succ n ih => simp only [sumBoxes, ih, Finset.sum_range_succ, add]

theorem gauss23_criticalValueBox_eq_sums (m d : ℤ) : gauss23CriticalValueBox m d =
    ⟨∑ j ∈ Finset.range 16, (gauss23CriticalPanelBox m d j).lo,
      ∑ j ∈ Finset.range 16, (gauss23CriticalPanelBox m d j).hi⟩ :=
  sumBoxes_eq_sums (gauss23CriticalPanelBox m d) 16

theorem gauss23_valueBox_contains (m : ℤ) {d : ℤ} (hd : 0 < d)
    (hphase : ∀ j i, gauss23PhaseCheck m d j i = true) :
    Contains (gauss23CriticalValueBox m d) (gauss23CriticalFiniteSum ((m : ℝ) / d)) := by
  unfold gauss23CriticalFiniteSum gauss23CriticalValueBox
  apply sumBoxes_contains
  intro j _
  unfold gauss23CriticalPanelBox
  apply sumBoxes_contains
  intro i _
  exact gauss23_sampleBox_contains m hd (Fin.ofNat 16 j) (Fin.ofNat 24 i) (hphase _ _)

#print axioms gauss23_criticalReading_eq_sum
#print axioms gauss23_valueBox_contains
#print axioms gauss23_criticalValueBox_eq_sums

end

end FieldTarget
