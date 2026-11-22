import SuperZeta.QuarterLine.QuartetBandParts
import SuperZeta.QuarterLine.QuartetBandTail
import SuperZeta.QuarterLine.QuarterScalar

namespace SuperZeta.QuartetBandDominance
noncomputable section
open Real Complex UnitSpectrum QuartetLeading QuartetShiftContinuation
open scoped ComplexConjugate

/-- The non-leading terms of the original spectrum throughout the high band. -/
theorem band_absolute_error {s : ℂ} (hl : 7/32 ≤ s.re) (hr : s.re ≤ 9/32) (ht : 100 ≤ s.im) :
    ‖continuation s - first ^ (-2*s)‖ ≤ 70*(s.im+2)*Real.exp (11*s.im/10) := by
  have hp : 0 ≤ s.re := by linarith
  have hi : 0 ≤ s.im := by linarith
  have hq : ‖s‖ ≤ s.im+1 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hp,abs_of_nonneg hi] at h
    linarith
  have hpi : ‖2*(π:ℂ)^(-2*s)‖ ≤ 2 := by
    rw [norm_mul,Complex.norm_ofNat]
    linarith [band_pi hp]
  have h2r : (2*s).re = 2*s.re := by simp [mul_re]
  have h2i : (2*s).im = 2*s.im := by simp [mul_im]
  have hz := band_zeta (w:=2*s) (by rw [h2r]; linarith)
    (by rw [h2r]; linarith) (by rw [h2i]; linarith)
  rw [norm_mul,Complex.norm_ofNat] at hz
  have hzeta : ‖2*(π:ℂ)^(-2*s)*riemannZeta (2*s)‖ ≤ 2*(2+3*(2*‖s‖)) := by
    rw [norm_mul]
    exact mul_le_mul hpi hz (norm_nonneg _) (by norm_num)
  have hc : ‖conj first^(-2*s)-2*(π:ℂ)^(-2*s)‖ ≤ 3 :=
    (norm_sub_le _ _).trans (by linarith [band_small_conjugate hp hi])
  have hh : ‖(dottie:ℂ)^(-2*s) + 2*(π:ℂ)^(-2*s)*riemannZeta (2*s) +
      (conj first^(-2*s)-2*(π:ℂ)^(-2*s))‖ ≤ 11+12*‖s‖ := by
    apply (norm_add_le _ _).trans
    linarith [norm_add_le ((dottie:ℂ)^(-2*s)) (2*(π:ℂ)^(-2*s)*riemannZeta (2*s)), band_dottie hr]
  have hex : 2 ≤ Real.exp (11*s.im/10) := by linarith [Real.add_one_le_exp (11*s.im/10)]
  have tail := QuartetBandTail.tail_band hl
  rw [abs_of_nonneg hi] at tail
  change ‖continuation s - upper 0^(-2*s)‖ ≤ _
  rw [band_sub_leading_eq hl hr ht]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (11+12*‖s‖) + 60*‖s‖*Real.exp (11*s.im/10) := add_le_add hh tail
    _ ≤ (6+66*‖s‖)*Real.exp (11*s.im/10) := by
      nlinarith only [mul_le_mul_of_nonneg_left hex (show 0 ≤ 6+6*‖s‖ by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- Relative error throughout the closed vertical band, with no approximation inputs. -/
theorem band_relative_error {s : ℂ} (hl : 7/32 ≤ s.re) (hr : s.re ≤ 9/32) (ht : 100 ≤ s.im) :
    ‖continuation s / (upper 0)^(-2*s) - 1‖ < (1/128:ℝ) := by
  let L := first^(-2*s)
  have hp : 0 < ‖L‖ := by
    have := band_leading_lower hr (show 0≤s.im by linarith)
    exact lt_of_lt_of_le (by positivity) this
  have hn : L ≠ 0 := norm_pos_iff.mp hp
  change ‖continuation s / L - 1‖ < _
  rw [show continuation s / L - 1 = (continuation s-L)/L by field_simp, norm_div,div_lt_iff₀ hp]
  have hb := band_absolute_error hl hr ht
  have hm := mul_lt_mul_of_pos_right (QuarterScalar.band_margin ht) (Real.exp_pos (11*s.im/10))
  rw [←Real.exp_add,show 3*s.im/20+11*s.im/10=5*s.im/4 by ring] at hm
  have hd := band_leading_lower hr (show 0≤s.im by linarith)
  change ‖continuation s - first ^ (-2*s)‖ < (1/128) * ‖first ^(-2*s)‖
  linarith

end
end SuperZeta.QuartetBandDominance
