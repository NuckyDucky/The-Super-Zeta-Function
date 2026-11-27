import CenteredFoldedMellin
import DedekindDiscriminant23AdaptiveParameters

/-! The direct logarithmic model with the expansion center chosen independently
of its radial and lattice cutoffs. -/

namespace FieldTarget

open MeasureTheory Set Complex
open scoped Interval

noncomputable section

private def plusAmplitude (N : ℕ) (slope : Bool) (c : ℂ) (u : ℝ) : ℂ :=
  (if slope then (u : ℂ) else 1) *
    (Complex.exp ((c - 1) * (u : ℂ)) * discriminant23PhaseDensityUpTo N (u : ℂ))

private def minusAmplitude (N : ℕ) (slope : Bool) (c : ℂ) (u : ℝ) : ℂ :=
  (if slope then -(u : ℂ) else 1) *
    (Complex.exp (-c * (u : ℂ)) * discriminant23PhaseDensityUpTo N (u : ℂ))

private theorem plusAmplitude_continuous (N : ℕ) (slope : Bool) (c : ℂ) :
    Continuous (plusAmplitude N slope c) := by
  cases slope <;> unfold plusAmplitude discriminant23PhaseDensityUpTo
    discriminant23CharacterPolynomialUpTo <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

private theorem minusAmplitude_continuous (N : ℕ) (slope : Bool) (c : ℂ) :
    Continuous (minusAmplitude N slope c) := by
  cases slope <;> unfold minusAmplitude discriminant23PhaseDensityUpTo
    discriminant23CharacterPolynomialUpTo <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

private theorem centeredModel_eq (N : ℕ) (slope : Bool) {L : ℝ} (hL : 0 ≤ L) (c w : ℂ) :
    centeredFoldedMellin (plusAmplitude N slope c) (minusAmplitude N slope c) L (w - c) =
      if slope then deriv (discriminant23CharacterModelUpTo N (Real.exp L)) w
      else discriminant23CharacterModelUpTo N (Real.exp L) w := by
  have h (u : ℝ) : discriminant23PhaseDensityUpTo N (u : ℂ) =
      Complex.exp (u : ℂ) *
        (discriminant23CharacterPolynomialUpTo N
          (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
    simp only [discriminant23PhaseDensityUpTo, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, discriminant23_characterPolynomialUpTo_ofReal]
  have hp (u : ℝ) : Complex.exp ((c - 1) * (u : ℂ)) * Complex.exp (u : ℂ) *
      Complex.exp ((u : ℂ) * (w - c)) = Complex.exp (w * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hm (u : ℝ) : Complex.exp (-c * (u : ℂ)) * Complex.exp (u : ℂ) *
      Complex.exp (-((u : ℂ) * (w - c))) = Complex.exp ((1 - w) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  cases slope
  · simp only [Bool.false_eq_true, ↓reduceIte, discriminant23_characterModelUpTo_eq_logIntegral,
      centeredFoldedMellin, plusAmplitude, minusAmplitude, one_mul]
    apply intervalIntegral.integral_congr
    intro u _
    beta_reduce
    rw [h, ← hp, ← hm]
    ring
  · simp only [↓reduceIte, discriminant23_characterModelUpTo_deriv_eq_logIntegral N hL,
      centeredFoldedMellin, plusAmplitude, minusAmplitude]
    apply intervalIntegral.integral_congr
    intro u _
    beta_reduce
    rw [h, ← hp, ← hm]
    ring

private theorem centered_amplitudes_norm_le (N : ℕ) (slope : Bool) {L u : ℝ} {c : ℂ}
    (hc : c.re ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc 0 L) :
    ‖plusAmplitude N slope c u‖ + ‖minusAmplitude N slope c u‖ ≤
      2 * (discriminant23PhaseTermCount N : ℝ) * (if slope then L else 1) := by
  have hp (v : ℂ) (hv : v.re ≤ 0) : ‖Complex.exp (v * (u : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact (Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hv hu.1)).trans_eq Real.exp_zero
  have hp₁ := hp (c - 1) (by rw [Complex.sub_re, Complex.one_re]; exact sub_nonpos.mpr hc.2)
  have hp₂ := hp (-c) (by rw [Complex.neg_re]; exact neg_nonpos.mpr hc.1)
  have hN : ‖discriminant23PhaseDensityUpTo N (u : ℂ)‖ ≤ (discriminant23PhaseTermCount N : ℝ) :=
    discriminant23_phaseDensity_real_norm_le N u
  have hPoint (z : ℂ) (hz : ‖z‖ ≤ 1) (v : ℂ) (hv : ‖v‖ ≤ if slope then L else 1) :
      ‖v * (z * discriminant23PhaseDensityUpTo N (u : ℂ))‖ ≤
        (if slope then L else 1) * (discriminant23PhaseTermCount N : ℝ) := by
    rw [norm_mul, norm_mul]
    have hB : 0 ≤ if slope then L else 1 := (norm_nonneg _).trans hv
    exact (mul_le_mul hv (mul_le_mul hz hN (norm_nonneg _) zero_le_one)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB).trans_eq (by rw [one_mul])
  have hs (sign : Bool) : ‖(if slope then (if sign then (u : ℂ) else -(u : ℂ)) else 1)‖ ≤
      if slope then L else 1 := by
    cases slope <;> cases sign <;> simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1, hu.2]
  have h₁ := hPoint _ hp₁ _ (hs true)
  have h₂ := hPoint _ hp₂ _ (hs false)
  unfold plusAmplitude minusAmplitude
  refine (add_le_add h₁ h₂).trans_eq ?_
  ring

/-- Each coefficient is a finite logarithmic integral at the center. -/
def discriminant23CenteredCoeff (N : ℕ) (L : ℝ) (slope : Bool) (c : ℂ) (k : ℕ) : ℂ :=
  centeredFoldedMellinCoeff (plusAmplitude N slope c) (minusAmplitude N slope c) L k

def discriminant23CenteredTaylor (N : ℕ) (L : ℝ) (slope : Bool) (c : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, discriminant23CenteredCoeff N L slope c k * (w - c) ^ k

def discriminant23CenteredTaylorError (N order : ℕ) (L r : ℝ) (slope : Bool) (n : ℕ) : ℝ :=
  discriminant23CharacterModelError order (Real.exp L) +
    4 * L * (discriminant23PhaseTermCount N : ℝ) * (if slope then L else 1) *
      (L * r) ^ n / (n.factorial : ℝ)

theorem discriminant23_centeredTaylor_error_le {N order : ℕ} {L r : ℝ}
    (slope : Bool) (n : ℕ) (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1))
    (hL : 0 ≤ L) (hRatio : L * r / (n + 1 : ℕ) ≤ 1 / 2) {c w : ℂ}
    (hc : c.re ∈ Icc (0 : ℝ) 1) (hw : w.re ∈ Icc (0 : ℝ) 1) (hz : ‖w - c‖ ≤ r) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23CenteredTaylor N L slope c n w‖ ≤
      discriminant23CenteredTaylorError N order L r slope n := by
  let model := discriminant23CharacterModelUpTo N (Real.exp L)
  let m := if slope then deriv model w else model w
  have hR : 1 ≤ Real.exp L := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hL
  have hModel : ‖(if slope then deriv discriminant23CharacterFold w else
      discriminant23CharacterFold w) - m‖ ≤ discriminant23CharacterModelError order (Real.exp L) := by
    cases slope
    · exact discriminant23_characterModelUpTo_error hOrder hCut hR
        (by linarith only [hw.1]) (by linarith only [hw.2])
    · have h := discriminant23_characterModelUpTo_iteratedDeriv_error 1 hOrder hCut hR hw.1 hw.2
      simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, m, model, ↓reduceIte] using h
  have hTaylor := centeredFoldedMellin_error_le (plusAmplitude_continuous N slope c)
    (minusAmplitude_continuous N slope c) hL (fun u hu ↦ centered_amplitudes_norm_le N slope hc hu)
    n hRatio hz
  rw [centeredModel_eq N slope hL] at hTaylor
  refine (norm_sub_le_norm_sub_add_norm_sub _ m _).trans ((add_le_add hModel hTaylor).trans_eq ?_)
  unfold discriminant23CenteredTaylorError
  ring

end

#check @discriminant23_centeredTaylor_error_le
#print axioms discriminant23_centeredTaylor_error_le

end FieldTarget
