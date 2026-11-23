import DottieReferencePhase
import Mathlib.Analysis.Real.Pi.Bounds

/-! A rational phase enclosure for the original Dottie reference point. -/

open Complex

namespace QuarticModel

open SuperZeta.StirlingCorrection

private theorem log_two_enclosure :
    0.693147180559945309417232121458 < Real.log 2 ∧
    Real.log 2 < 0.693147180559945309417232121459 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/2 : ℝ)) (by norm_num) 110
  rw [show (1 : ℝ) - 1/2 = 2⁻¹ by norm_num, Real.log_inv] at h
  norm_num1 at h
  obtain ⟨hl, hh⟩ := abs_le.mp h
  constructor <;> linarith

private theorem split_log {r : ℝ} (hr : 0 < r) :
    Real.log r = 42 * Real.log 2 + Real.log (r / 2^42) := by
  have he : (2:ℝ)^42 * (r / 2^42) = r := mul_div_cancel₀ r (by norm_num)
  calc
    Real.log r = Real.log ((2:ℝ)^42 * (r / 2^42)) := congrArg Real.log he.symm
    _ = Real.log ((2:ℝ)^42) + Real.log (r / 2^42) :=
      Real.log_mul (by norm_num) (div_ne_zero hr.ne' (by norm_num))
    _ = _ := by rw [Real.log_pow]; norm_num

private theorem log_reference_lower :
    29.14088602657451053933 < Real.log 4526119322477.943440190398 := by
  let r : ℝ := 4526119322477.943440190398
  change _ < Real.log r
  have e : (1:ℝ) - (1-r/2^42) = r/2^42 := by ring
  have h := Real.abs_log_sub_add_sum_range_le (x := 1-r/2^42) (by norm_num [r]) 18
  rw [e] at h
  dsimp only [r] at h
  norm_num1 at h
  rw [split_log (by norm_num [r])]
  dsimp only [r]
  have hlo := log_two_enclosure.1
  obtain ⟨hl, _⟩ := abs_le.mp h
  linarith

private theorem log_reference_upper :
    Real.log 4526119322477.943440204808 < 29.14088602657451053934 := by
  let r : ℝ := 4526119322477.943440204808
  change Real.log r < _
  have e : (1:ℝ) - (1-r/2^42) = r/2^42 := by ring
  have h := Real.abs_log_sub_add_sum_range_le (x := 1-r/2^42) (by norm_num [r]) 18
  rw [e] at h
  dsimp only [r] at h
  norm_num1 at h
  rw [split_log (by norm_num [r])]
  dsimp only [r]
  have hhi := log_two_enclosure.2
  obtain ⟨_, hh⟩ := abs_le.mp h
  linarith

/-- Stable log norm shared by the reference phase and relative contour. -/
theorem dottie_reference_norm_log_interval :
    let t := dottieHeight - 1/512
    let z : ℂ := 1/2 + (t : ℂ) * I
    29.14088602657451053933 < Real.log ‖z‖ ∧
      Real.log ‖z‖ < 29.14088602657451053934 := by
  let t := dottieHeight - 1/512
  let z : ℂ := 1/2 + (t : ℂ) * I
  change 29.14088602657451053933 < Real.log ‖z‖ ∧
    Real.log ‖z‖ < 29.14088602657451053934
  have htlo : 4526119322477.943440190398 < t := by
    dsimp [t]
    linarith [dottieHeight_enclosure.1]
  have hthi : t + 1/10^12 < 4526119322477.943440204808 := by
    dsimp [t]
    linarith [dottieHeight_enclosure.2]
  have ht : 4*10^12 < t := by linarith
  have htpos : 0 < t := by linarith
  have hnorm : ‖z‖ ^ 2 = t^2 + 1/4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, Complex.mul_re, Complex.mul_im]
    ring
  have hle : t ≤ ‖z‖ := by
    have him : z.im = t := by simp [z, Complex.mul_im]
    simpa [him, abs_of_pos htpos] using Complex.abs_im_le_norm z
  have hnhi : ‖z‖ < t + 1/10^12 := by
    by_contra! h
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ t+1/10^12) h 2
    rw [hnorm] at hs
    nlinarith
  have hlo := log_reference_lower.trans <|
    Real.log_lt_log (by norm_num) (htlo.trans_le hle)
  have hhi := (Real.log_lt_log (htpos.trans_le hle) (hnhi.trans hthi)).trans log_reference_upper
  exact ⟨hlo,hhi⟩

/-- The exact unit Gamma value at the original reference point has a phase
in a two-microradian-wide interval. -/
theorem dottie_gamma_reference_phase_interval :
    let t := dottieHeight - 1/512
    let z : ℂ := 1/2 + (t : ℂ) * I
    ∃ phase : ℝ, 4.067324 < phase ∧ phase < 4.067326 ∧
      Gamma z / (‖Gamma z‖ : ℂ) = Complex.exp ((phase : ℂ) * I) := by
  let t := dottieHeight - 1/512
  let z : ℂ := 1/2 + (t : ℂ) * I
  change ∃ phase : ℝ, 4.067324 < phase ∧ phase < 4.067326 ∧
    Gamma z / (‖Gamma z‖ : ℂ) = Complex.exp ((phase : ℂ) * I)
  have htlo : 4526119322477.943440190398 < t := by
    dsimp [t]
    linarith [dottieHeight_enclosure.1]
  have hthi : t + 1/10^12 < 4526119322477.943440204808 := by
    dsimp [t]
    linarith [dottieHeight_enclosure.2]
  have htpos : 0 < t := by linarith
  obtain ⟨hlo,hhi⟩ := dottie_reference_norm_log_interval
  have pl : 4526119322477.943440190398 * (29.14088602657451053933 - 1) ≤
      t * (Real.log ‖z‖ - 1) :=
    mul_le_mul htlo.le (sub_le_sub_right hlo.le 1) (by norm_num) htpos.le
  have pu : t * (Real.log ‖z‖ - 1) ≤
      4526119322477.943440204808 * (29.14088602657451053934 - 1) := by
    apply mul_le_mul (by linarith only [hthi]) (sub_le_sub_right hhi.le 1) _
      (by norm_num)
    linarith
  obtain ⟨e, he, hp⟩ := dottie_gamma_reference_phase
  have he' := abs_lt.mp he
  let phase := t*(Real.log ‖z‖-1) + e - 2*Real.pi*20271407219358
  refine ⟨phase, ?_, ?_, ?_⟩
  · dsimp only [phase]
    linarith only [pl, he'.1, Real.pi_lt_d20]
  · dsimp only [phase]
    linarith only [pu, he'.2, Real.pi_gt_d20]
  change Gamma z / (‖Gamma z‖ : ℂ) = Complex.exp (((t * (Real.log ‖z‖ - 1) + e : ℝ) : ℂ) * I) at hp
  rw [hp, show ((↑(t * (Real.log ‖z‖ - 1) + e) : ℂ) * I) =
      (phase : ℂ) * I + (20271407219358 : ℕ) * (2 * (Real.pi : ℂ) * I) by
    dsimp only [phase]
    push_cast
    ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

#print axioms dottie_reference_norm_log_interval
#print axioms dottie_gamma_reference_phase_interval

end QuarticModel
