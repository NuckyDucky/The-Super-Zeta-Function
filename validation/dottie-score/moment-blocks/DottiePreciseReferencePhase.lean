import DottieSharpRelativeCircle
import DottiePreciseHeight

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open private binary_log_bound from DottieCompletedReferencePhase
open private log_two_enclosure from DottieReferencePhaseEnclosure
open private normalized_exp from DottieGammaPhase
open private dottie_pi_lower dottie_pi_upper from DottiePreciseHeight

set_option autoImplicit false
set_option maxHeartbeats 750000

private theorem precise_log_discriminant :
    30.90853456234470711944531413 < Real.log 26509772707289 ∧
      Real.log 26509772707289 < 30.90853456234470711944531415 := by
  have h := binary_log_bound (r := 26509772707289) (by norm_num) 45 52 (by norm_num)
  norm_num1 at h
  obtain ⟨hl, hh⟩ := abs_le.mp h
  constructor <;> linarith only [hl, hh, log_two_enclosure.1, log_two_enclosure.2]

private theorem precise_log_pi :
    1.14472988584940017414342735 < Real.log Real.pi ∧
      Real.log Real.pi < 1.14472988584940017414342736 := by
  constructor
  · have h := binary_log_bound (r := 3.14159265358979323846264338327950)
      (by norm_num) 2 52 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log (by norm_num) dottie_pi_lower
    linarith only [(abs_le.mp h).1, log_two_enclosure.1, hp]
  · have h := binary_log_bound (r := 3.14159265358979323846264338327951)
      (by norm_num) 2 52 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log Real.pi_pos dottie_pi_upper
    linarith only [(abs_le.mp h).2, log_two_enclosure.2, hp]

private theorem precise_reference_height :
    4526119322477.94344019420732885690 < dottieHeight - 1 / 512 ∧
      dottieHeight - 1 / 512 < 4526119322477.94344019420732885700 := by
  obtain ⟨hl, hh⟩ := dottieHeight_precise_enclosure
  constructor <;> linarith only [hl, hh]

private theorem precise_reference_norm_log :
    29.14088602657451053933602766 < Real.log ‖dottieReferencePoint‖ ∧
      Real.log ‖dottieReferencePoint‖ < 29.14088602657451053933602769 := by
  let t := dottieHeight - 1 / 512
  have ht : 4 * 10^12 < t := by dsimp only [t]; linarith only [precise_reference_height.1]
  have ht₀ : 0 < t := by linarith only [ht]
  have hn : ‖dottieReferencePoint‖ ^ 2 = t^2 + 1/4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [dottieReferencePoint, Complex.mul_re, Complex.mul_im, t]
    ring
  have hle : t ≤ ‖dottieReferencePoint‖ := by
    have him : dottieReferencePoint.im = t := by
      simp [dottieReferencePoint, Complex.mul_im, t]
    simpa only [him, abs_of_pos ht₀] using Complex.abs_im_le_norm dottieReferencePoint
  have hhi : ‖dottieReferencePoint‖ < t + 1 / 10^13 := by
    by_contra! h
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ t + 1 / 10^13) h 2
    rw [hn] at hs
    nlinarith only [hs, ht]
  have hlo : 4526119322477.94344019420732885690 < ‖dottieReferencePoint‖ :=
    precise_reference_height.1.trans_le hle
  have hup : ‖dottieReferencePoint‖ < 4526119322477.94344019420742885700 := by
    dsimp only [t] at hhi
    linarith only [hhi, precise_reference_height.2]
  constructor
  · have h := binary_log_bound (r := 4526119322477.94344019420732885690)
      (by norm_num) 42 26 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log (by norm_num) hlo
    linarith only [(abs_le.mp h).1, log_two_enclosure.1, hp]
  · have h := binary_log_bound (r := 4526119322477.94344019420742885700)
      (by norm_num) 42 26 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log (ht₀.trans_le hle) hup
    linarith only [(abs_le.mp h).2, log_two_enclosure.2, hp]

private theorem precise_reference_log_sum :
    42.45042342189746392491525736 <
      Real.log archivedThetaScale + Real.log ‖dottieReferencePoint‖ - 1 ∧
    Real.log archivedThetaScale + Real.log ‖dottieReferencePoint‖ - 1 <
      42.45042342189746392491525742 := by
  unfold archivedThetaScale
  rw [Real.log_div (by positivity) Real.pi_ne_zero, Real.log_sqrt (by norm_num)]
  obtain ⟨hd₀, hd₁⟩ := precise_log_discriminant
  obtain ⟨hp₀, hp₁⟩ := precise_log_pi
  obtain ⟨hz₀, hz₁⟩ := precise_reference_norm_log
  constructor <;> linarith only [hd₀, hd₁, hp₀, hp₁, hz₀, hz₁]

/-- A single rational phase for evaluating the projected reading directly. -/
theorem dottie_sharp_reference_unit_precise_phase :
    ∃ phase : ℝ, |phase - 3.92292489981824| ≤ 1 / (2 * 10^12) ∧
      dottieSharpReferenceUnit = Complex.exp ((phase : ℂ) * I) := by
  let t := dottieHeight - 1 / 512
  let z := dottieReferencePoint
  let B := archivedThetaScale
  let b := (B : ℂ)^z
  let A := archivedDottieCompletionScale
  let L := Real.log B + Real.log ‖z‖ - 1
  obtain ⟨e, he, hg⟩ := dottie_gamma_reference_phase
  let phase := t * L - 2 * Real.pi * 30579343486443 + e
  have htlo : 4526119322477.94344019420732885690 < t := precise_reference_height.1
  have hthi : t < 4526119322477.94344019420732885700 := precise_reference_height.2
  have hLlo : 42.45042342189746392491525736 < L := precise_reference_log_sum.1
  have hLhi : L < 42.45042342189746392491525742 := precise_reference_log_sum.2
  have hprodlo := mul_le_mul htlo.le hLlo.le (by norm_num) (by linarith only [htlo])
  have hprodhi := mul_le_mul hthi.le hLhi.le (by linarith only [hLlo]) (by norm_num)
  obtain ⟨hel, heu⟩ := abs_lt.mp he
  have hphase : |phase - 3.92292489981824| ≤ 1 / (2 * 10^12) := by
    apply abs_le.mpr
    dsimp only [phase]
    constructor
    · linarith only [hprodlo, hel, dottie_pi_upper]
    · linarith only [hprodhi, heu, dottie_pi_lower]
  refine ⟨phase, hphase, ?_⟩
  have hB : 0 < B := archivedThetaScale_pos
  have hb₀ : (B : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB.ne'
  have hb : b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hb₀)
  have hz₀ : 0 < z.re := by norm_num [z, dottieReferencePoint, Complex.mul_re]
  have hg₀ := Gamma_ne_zero_of_re_pos hz₀
  have hA : 0 < A := archivedDottieCompletionScale_pos
  have hunit : dottieSharpReferenceUnit =
      (b / (‖b‖ : ℂ)) * (Gamma z / (‖Gamma z‖ : ℂ)) := by
    change (b * Gamma z / (A : ℂ)) / (‖b * Gamma z / (A : ℂ)‖ : ℂ) = _
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
      Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [ofReal_ne_zero.mpr hA.ne',
      ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb),
      ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg₀)]
  have hbphase : b / (‖b‖ : ℂ) = Complex.exp (((t * Real.log B : ℝ) : ℂ) * I) := by
    dsimp only [b]
    rw [Complex.cpow_def_of_ne_zero hb₀, normalized_exp]
    have hz : z.im = t := by simp [z, t, dottieReferencePoint, Complex.mul_im]
    rw [← Complex.ofReal_log hB.le, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hz, mul_comm (Real.log B) t]
  have hgphase : Gamma z / (‖Gamma z‖ : ℂ) =
    Complex.exp (((t * (Real.log ‖z‖ - 1) + e : ℝ) : ℂ) * I) := hg
  rw [hunit, hbphase, hgphase, ← Complex.exp_add]
  have hperiod : ((t * Real.log B : ℝ) : ℂ) * I +
      ((t * (Real.log ‖z‖ - 1) + e : ℝ) : ℂ) * I =
        (phase : ℂ) * I + (30579343486443 : ℕ) * (2 * (Real.pi : ℂ) * I) := by
    dsimp only [phase, L]
    push_cast
    ring
  rw [hperiod, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

#print axioms dottie_sharp_reference_unit_precise_phase

end QuarticModel
