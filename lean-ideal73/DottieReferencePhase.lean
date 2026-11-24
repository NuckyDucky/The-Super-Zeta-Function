import ArchivedDottieHeight
import DottieGammaPhase

/-! Convert the Gamma phase estimate at the measured Dottie height into a
numerical enclosure for the original Gaussian reference normalization. -/

open Complex

namespace QuarticModel

open SuperZeta.StirlingCorrection

/-- The Gamma phase error is less than (10^{-13}) throughout the archived
heights. This includes the base phase at (T_D) and the reference at
(T_D-1/512). -/
theorem dottie_gamma_phase_near_height {z : ℂ} (hz : 0 < z.re)
    (hy : |z.im - dottieHeight| ≤ 1/16) :
    ∃ error : ℝ, |error| < 1 / 10^13 ∧
      Gamma z / (‖Gamma z‖ : ℂ) =
      Complex.exp ((((z-1/2)*Complex.log z-z).im + error : ℝ) * I) := by
  have ht : 4*10^12 < z.im := by
    have hlo := (abs_le.mp hy).1
    linarith [dottieHeight_enclosure.1]
  have hpos : 0 < z.im := by linarith
  obtain ⟨e, he, hphase⟩ := dottie_gamma_phase_with_error hz
    (by rw [abs_of_pos hpos]; linarith)
  refine ⟨e, he.trans_lt ?_, hphase⟩
  rw [abs_of_pos hpos]
  apply (div_lt_div_iff₀ (by positivity : (0:ℝ) < 3*z.im) (by norm_num)).2
  linarith

/-- The phase at the point used to normalize the retained and omitted
norm sums. -/
theorem dottie_gamma_reference_phase :
    let t := dottieHeight - 1/512
    let z : ℂ := 1/2 + (t : ℂ) * I
    ∃ error : ℝ, |error| < 1 / 10^13 ∧
      Gamma z / (‖Gamma z‖ : ℂ) =
      Complex.exp (((t * (Real.log ‖z‖ - 1) + error : ℝ) : ℂ) * I) := by
  dsimp only
  let t := dottieHeight - 1/512
  let z : ℂ := 1/2 + (t : ℂ) * I
  have hr : z.re = 1/2 := by simp [z, Complex.mul_re]
  have hi : z.im = t := by simp [z, Complex.mul_im]
  have hy : |z.im - dottieHeight| ≤ 1/16 := by
    rw [hi]
    have he : t - dottieHeight = -(1/512 : ℝ) := by dsimp [t]; ring
    rw [he]
    norm_num
  have he : ((z-1/2)*Complex.log z-z).im = t * (Real.log ‖z‖ - 1) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.sub_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_im, Complex.one_re, hr, hi, sub_self,
      zero_mul, zero_add, Complex.log_re]
    ring
  obtain ⟨e, h, hp⟩ := dottie_gamma_phase_near_height (by rw [hr]; norm_num) hy
  rw [he] at hp
  exact ⟨e, h, hp⟩

#print axioms dottie_gamma_phase_near_height
#print axioms dottie_gamma_reference_phase

end QuarticModel
