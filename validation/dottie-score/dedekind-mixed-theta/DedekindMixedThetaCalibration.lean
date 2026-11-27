import DedekindMixedThetaSampleModel

/-! The sampled mixed-theta contour reads the completed Dedekind zeta of
the field at the original input. The same completion scales the reference. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Metric
open scoped NNReal

noncomputable section

/-- Recover the completed value of any identified Dedekind continuation. -/
theorem mixedThetaCompletedReading_eq_gamma_mul (K : Type*) [Field K] [NumberField K]
    {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z) {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading K w = dedekindGammaFactor K w * Z w := by
  have h0 : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h1 : w ≠ 1 := by rintro rfl; norm_num at hhi
  have hp := mul_ne_zero h0 (sub_ne_zero.mpr h1.symm)
  rw [mixedThetaCompletedReading, mixedThetaSignedReading, mul_div_cancel_left₀ _ hp,
    continuation_eq_off_one (mixedThetaContinuation_isDedekind K) hZ h1]

/-- Applying the field completion to both values keeps their relative
error budget in either direction. -/
theorem mixedThetaCompletedReading_relative_bound_iff
    (K : Type*) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    {w P : ℂ} {q : ℝ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    ‖mixedThetaCompletedReading K w - dedekindGammaFactor K w * P‖ ≤
      q * ‖dedekindGammaFactor K w * P‖ ↔ ‖Z w - P‖ ≤ q * ‖P‖ := by
  rw [mixedThetaCompletedReading_eq_gamma_mul K hZ hlo hhi, ← mul_sub,
    norm_mul, norm_mul, mul_left_comm q]
  exact mul_le_mul_iff_right₀ (norm_pos_iff.mpr (dedekindGammaFactor_ne_zero K hlo))

theorem mixedThetaCompletedReading_weighted_eq
    (K : Type*) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) (W : ℂ) :
    (W / dedekindGammaFactor K w) * mixedThetaCompletedReading K w = W * Z w := by
  rw [mixedThetaCompletedReading_eq_gamma_mul K hZ hlo hhi, ← mul_assoc,
    div_mul_cancel₀ W (dedekindGammaFactor_ne_zero K hlo)]

/-- The disk test can take sample enclosures from any exact realization of
the Dedekind continuation, using its own completion at each sample. -/
theorem dedekindZeta_ne_zero_of_completed_sample_model
    (K : Type) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    {c w ω : ℂ} {P : ℂ → ℂ} {R : ℝ≥0} {h r ε q : ℝ} {N n : ℕ} (samples : ℕ → ℂ)
    (hleft : 0 < c.re - R) (hright : 0 < 1 - c.re - R)
    (hN : 0 < N) (hn : n ≤ N) (hω : IsPrimitiveRoot ω N) (hunit : ‖ω‖ = 1)
    (hr₀ : 0 < r) (hr : r < h) (hh : h < (R : ℝ)) (hq : q < 1)
    (hSamples : ∀ j < N, let z := c + (h : ℂ) * ω ^ j
      ‖samples j - dedekindGammaFactor K z * Z z‖ ≤ ε)
    (hP : DifferentiableOn ℂ P (closedBall c r))
    (hPne : ∀ z ∈ closedBall c r, P z ≠ 0)
    (hBoundary : ∀ z ∈ sphere c r,
      ‖contourSamplePolynomial samples ω N n ((z - c) / (h : ℂ)) - P z‖ +
        mixedThetaContourSampleError K c R h r ε N n ≤ q * ‖P z‖)
    (hw : w ∈ closedBall c r) : Z w ≠ 0 := by
  have hstrip {z : ℂ} (hz : z ∈ closedBall c (R : ℝ)) : 0 < z.re ∧ z.re < 1 := by
    have hn := mem_closedBall.mp hz
    rw [dist_eq_norm] at hn
    have hc := abs_le.mp ((abs_re_le_norm (z - c)).trans hn)
    rw [sub_re] at hc
    exact ⟨by linarith only [hleft, hc.1], by linarith only [hright, hc.2]⟩
  have hvalues (j : ℕ) (hj : j < N) :
      ‖samples j - mixedThetaCompletedReading K (c + (h : ℂ) * ω ^ j)‖ ≤ ε := by
    have hjBall : c + (h : ℂ) * ω ^ j ∈ closedBall c (R : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_pow,
        hunit, one_pow, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (hr₀.trans hr)]
      exact hh.le
    have hjs := hstrip hjBall
    rw [mixedThetaCompletedReading_eq_gamma_mul K hZ hjs.1 hjs.2]
    exact hSamples j hj
  have hws := hstrip (closedBall_subset_closedBall (hr.trans hh).le hw)
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hws
  rw [← continuation_eq_off_one (mixedThetaContinuation_isDedekind K) hZ hw1]
  exact mixedThetaContinuation_ne_zero_of_sample_model K samples hleft hright
    hN hn hω hunit hr₀ hr hh hq hvalues hP hPne hBoundary hw

#check @dedekindZeta_ne_zero_of_completed_sample_model
#print axioms mixedThetaCompletedReading_eq_gamma_mul
#print axioms mixedThetaCompletedReading_relative_bound_iff
#print axioms mixedThetaCompletedReading_weighted_eq
#print axioms dedekindZeta_ne_zero_of_completed_sample_model

end

end FieldTarget
