import SuperZeta.QuarterLine.QuartetLeadingParts
import SuperZeta.QuarterLine.QuartetShiftContinuation
import SuperZeta.QuarterLine.QuartetShiftBoundsApplied
import SuperZeta.QuarterLine.DominanceCriterion
import SuperZeta.QuarterLine.QuarterEuler

namespace SuperZeta.QuartetDominance
noncomputable section
open Real Complex UnitSpectrum QuartetShiftContinuation QuartetLeading
open scoped ComplexConjugate

/-- Select the member of the first conjugate pair that grows at height t. -/
def dominant (t : ℝ) : ℂ :=
  if 0 ≤ t then first ^ (-2*quarter t) else (conj first) ^ (-2*quarter t)

private def opposite (t : ℝ) : ℂ :=
  if 0 ≤ t then (conj first) ^ (-2*quarter t) else first ^ (-2*quarter t)

theorem dominant_lower (t : ℝ) :
    Real.exp (5*|t|/4)/2 ≤ ‖dominant t‖ := by
  by_cases h : 0 ≤ t
  · rw [dominant,if_pos h,abs_of_nonneg h]
    convert norm_leading_lower h using 1
    ring_nf
  · rw [dominant,if_neg h,abs_of_neg (lt_of_not_ge h), quarter, norm_conjugate_leading]
    convert norm_leading_lower (show 0≤ -t by linarith) using 1
    ring_nf

private theorem opposite_le (t : ℝ) : ‖opposite t‖ ≤ 1 := by
  by_cases h : 0 ≤ t
  · rw [opposite,if_pos h, quarter, norm_conjugate_leading]
    exact small_first (by linarith)
  · rw [opposite,if_neg h]
    exact small_first (by linarith)

private theorem residual_eq (t : ℝ) (ht : 1 ≤ |t|) :
    let s := quarter t
    continuation s - dominant t =
      (dottie:ℂ)^(-2*s) + 2*(Real.pi:ℂ)^(-2*s)*riemannZeta (2*s) +
      (opposite t - 2*(Real.pi:ℂ)^(-2*s)) + ∑' n, levelDiff (n+1) s := by
  dsimp only
  by_cases h : 0 ≤ t
  · simpa only [dominant,opposite,if_pos h] using quarter_sub_leading_eq t ht
  · simpa only [dominant,opposite,if_neg h] using quarter_sub_conj_leading_eq t ht

private theorem residual_bound {t : ℝ} (ht : 100 ≤ |t|)
    (tail : ‖∑' n, levelDiff (n+1) (quarter t)‖ ≤
      48*‖quarter t‖*Real.exp (11*|t|/10)) :
    ‖continuation (quarter t) - dominant t‖ ≤
      80*(|t|+2)*Real.exp (11*|t|/10) := by
  let s := quarter t
  have hq : ‖s‖ ≤ 1+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    change ‖s‖ ≤ |(1/4:ℝ)|+|t| at h
    rw [abs_of_nonneg (by norm_num : 0 ≤ (1/4:ℝ))] at h
    linarith
  have hpi : ‖2*(π:ℂ)^(-2*s)‖ ≤ 2 := by
    rw [norm_mul]; norm_num
    simpa only [neg_mul] using pi_power_le t
  have hr : (2*s).re = 1/2 := by norm_num [s,quarter,Complex.mul_re]
  have hi : (2*s).im ≠ 0 := by
    have h0 : t ≠ 0 := by rintro rfl; norm_num at ht
    simpa [s,quarter,Complex.mul_im] using h0
  have hz := QuarterEuler.zeta_half_bound hr hi
  rw [norm_mul] at hz
  norm_num only [Complex.norm_ofNat] at hz
  have hzeta : ‖2*(π:ℂ)^(-2*s)*riemannZeta (2*s)‖ ≤ 2*(1+2*(2*‖s‖)) := by
    rw [norm_mul]
    exact mul_le_mul hpi hz (norm_nonneg _) (by norm_num)
  have hc : ‖opposite t-2*(π:ℂ)^(-2*s)‖ ≤ 3 :=
    (norm_sub_le _ _).trans (by linarith [opposite_le t,hpi])
  have hd : ‖(dottie:ℂ)^(-2*s)‖ ≤ 2 := dottie_power_le t
  have hh : ‖(dottie:ℂ)^(-2*s) + 2*(π:ℂ)^(-2*s)*riemannZeta (2*s) +
      (opposite t-2*(π:ℂ)^(-2*s))‖ ≤ 7+8*‖s‖ := by
    apply (norm_add_le _ _).trans
    linarith [norm_add_le ((dottie:ℂ)^(-2*s)) (2*(π:ℂ)^(-2*s)*riemannZeta (2*s))]
  have hex : 1 ≤ Real.exp (11*|t|/10) := Real.one_le_exp (by positivity)
  rw [residual_eq t (by linarith)]
  apply (norm_add_le _ _).trans
  change ‖(dottie:ℂ)^(-2*s) + 2*(π:ℂ)^(-2*s)*riemannZeta (2*s) +
      (opposite t-2*(π:ℂ)^(-2*s))‖ + ‖∑' n, levelDiff (n+1) s‖ ≤ _
  calc
    _ ≤ (7+8*‖s‖) + 48*‖s‖*Real.exp (11*|t|/10) := add_le_add hh tail
    _ ≤ (7+56*‖s‖)*Real.exp (11*|t|/10) := by
      nlinarith only [mul_le_mul_of_nonneg_left hex (show 0 ≤ 7+8*‖s‖ by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) (Real.exp_pos _).le

/-- Absolute error when only the growing member of the first pair is retained. -/
theorem quarter_error {t : ℝ} (ht : 100 ≤ |t|) :
    ‖continuation (quarter t) - dominant t‖ ≤
      80*(|t|+2)*Real.exp (11*|t|/10) :=
  residual_bound ht (QuartetShiftBounds.tail_quarter t)

/-- Beyond either height 100, the true continuation is strictly closer to its
growing first-root contribution than that contribution is to zero. -/
theorem quarter_dominates {t : ℝ} (ht : 100 ≤ |t|) :
    ‖continuation (quarter t)-dominant t‖ < ‖dominant t‖ :=
  QuarterLine.dominates ht
    (quarter_error ht) (dominant_lower t)

/-- The original continued super zeta has no zero on either high quarter-line ray. -/
theorem quarter_nonzero {t : ℝ} (ht : 100 ≤ |t|) :
    UnitSpectrum.continuation (quarter t) ≠ 0 :=
  QuarterLine.nonzero_of_dominates (quarter_dominates ht)

end
end SuperZeta.QuartetDominance
