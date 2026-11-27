import DedekindMixedThetaCompletedRings
import DedekindMixedThetaOscillation
import DottieRationalContour

namespace FieldTarget

open Complex MeasureTheory Set SuperZeta.StirlingCorrection
open DedekindZetaZeroFree.AbelianQuotient

noncomputable section

/-- A uniform modulus-of-variation constant for the exact pole correction on
a disk missing both poles. -/
def contourPoleVariation (a c : ℂ) (r : ℝ) : ℝ :=
  ‖a‖ * (1 + 2 * (‖c‖ + r)) / (((‖c‖ - r) * (‖1 - c‖ - r)) ^ 2)

theorem contourPoleDifference_le {a c w v : ℂ} {r : ℝ}
    (hc : r < ‖c‖) (hc1 : r < ‖1 - c‖)
    (hw : w ∈ Metric.closedBall c r) (hv : v ∈ Metric.closedBall c r) :
    ‖a / (w * (1 - w)) - a / (v * (1 - v))‖ ≤ contourPoleVariation a c r * ‖w - v‖ := by
  let d := (‖c‖ - r) * (‖1 - c‖ - r)
  have hd : 0 < d := mul_pos (sub_pos.mpr hc) (sub_pos.mpr hc1)
  have hdist (z : ℂ) (hz : z ∈ Metric.closedBall c r) : ‖z - c‖ ≤ r :=
    dist_eq_norm z c ▸ Metric.mem_closedBall.mp hz
  have hpos (z : ℂ) (hz : z ∈ Metric.closedBall c r) : d ≤ ‖z * (1 - z)‖ := by
    have h₀ : ‖c‖ ≤ ‖z‖ + ‖z - c‖ := by
      calc
        ‖c‖ = ‖z - (z - c)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h₁ : ‖1 - c‖ ≤ ‖1 - z‖ + ‖z - c‖ := by
      calc
        ‖1 - c‖ = ‖(1 - z) + (z - c)‖ := by rw [show (1 - z) + (z - c) = 1 - c by ring]
        _ ≤ _ := norm_add_le _ _
    rw [norm_mul]
    exact mul_le_mul (by linarith [hdist z hz]) (by linarith [hdist z hz])
      (sub_nonneg.mpr hc1.le) (norm_nonneg _)
  have hupper (z : ℂ) (hz : z ∈ Metric.closedBall c r) : ‖z‖ ≤ ‖c‖ + r := by
    calc
      ‖z‖ = ‖c + (z - c)‖ := by rw [add_sub_cancel]
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right (hdist z hz) _
  have hW := norm_pos_iff.mp (hd.trans_le (hpos w hw))
  have hV := norm_pos_iff.mp (hd.trans_le (hpos v hv))
  have hEq : a / (w * (1 - w)) - a / (v * (1 - v)) =
      (a * ((v - w) * (1 - w - v))) / ((w * (1 - w)) * (v * (1 - v))) := by
    field_simp [hW, hV, (mul_ne_zero_iff.mp hW).1, (mul_ne_zero_iff.mp hW).2,
      (mul_ne_zero_iff.mp hV).1, (mul_ne_zero_iff.mp hV).2]
    ring
  have hNumerator : ‖1 - w - v‖ ≤ 1 + 2 * (‖c‖ + r) := by
    calc
      _ ≤ ‖1 - w‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖w‖) + ‖v‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by rw [norm_one]; linarith [hupper w hw, hupper v hv]
  have hDenom : d^2 ≤ ‖w * (1 - w)‖ * ‖v * (1 - v)‖ := by
    rw [pow_two]
    exact mul_le_mul (hpos w hw) (hpos v hv) hd.le (norm_nonneg _)
  have hcr : 0 ≤ ‖c‖ + r :=
    (norm_nonneg w).trans (hupper w hw)
  calc
    _ = (‖a‖ * ‖1 - w - v‖ / (‖w * (1 - w)‖ * ‖v * (1 - v)‖)) * ‖w - v‖ := by
      rw [hEq, norm_div, norm_mul, norm_mul, norm_mul, norm_sub_rev v w]
      ring
    _ ≤ _ := by
      have hnum : 0 ≤ ‖a‖ * (1 + 2 * (‖c‖ + r)) :=
        mul_nonneg (norm_nonneg _) (by linarith)
      exact mul_le_mul_of_nonneg_right (div_le_div₀ hnum
        (mul_le_mul_of_nonneg_left hNumerator (norm_nonneg _)) (pow_pos hd 2) hDenom) (norm_nonneg _)

/-- The total contour variation of the retained Mellin part and exact pole
correction. -/
def mixedThetaContourVariation (K : Type) [Field K] [NumberField K] (R : ℝ) (c : ℂ)
    (r : ℝ) : ℝ :=
  2 * Real.log R * (∫ t : ℝ in 1..R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖)
    + contourPoleVariation (Theta.mixedThetaPair K).f₀ c r

theorem mixedThetaCompletedTruncation_difference_le_on_disk
    (K : Type) [Field K] [NumberField K] {R r : ℝ} (hR : 1 ≤ R) {c w v : ℂ}
    (hc : r < ‖c‖) (hc1 : r < ‖1 - c‖)
    (hw : w ∈ Metric.closedBall c r) (hv : v ∈ Metric.closedBall c r)
    (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) (hv₀ : 0 ≤ v.re) (hv₁ : v.re ≤ 1) :
    ‖mixedThetaCompletedTruncation K R w - mixedThetaCompletedTruncation K R v‖ ≤
      mixedThetaContourVariation K R c r * ‖w - v‖ := by
  let p := fun z : ℂ => (Theta.mixedThetaPair K).f₀ / (z * (1 - z))
  change ‖(mixedThetaTruncation K R w - p w) - (mixedThetaTruncation K R v - p v)‖ ≤ _
  rw [show (mixedThetaTruncation K R w - p w) - (mixedThetaTruncation K R v - p v) =
    (mixedThetaTruncation K R w - mixedThetaTruncation K R v) - (p w - p v) by ring]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (mixedThetaTruncation_difference_le K hR hw₀ hw₁ hv₀ hv₁)
    (contourPoleDifference_le (a := (Theta.mixedThetaPair K).f₀) hc hc1 hw hv)).trans_eq ?_
  unfold mixedThetaContourVariation
  ring

private theorem dottie_closedBall_avoids_poles (T : ℝ) (n : ℕ) :
    dottieScaledRadius n < ‖dottieScaledRightCenter T n‖ ∧
      dottieScaledRadius n < ‖1 - dottieScaledRightCenter T n‖ := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 ≤ r := by dsimp [r, dottieScaledRadius, dottieRingScale]; positivity
  have hl : c - (r : ℂ) ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm, show c - (r : ℂ) - c = -(r : ℂ) by ring]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hu : c + (r : ℂ) ∈ Metric.closedBall c r := by
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
  have hleft : (1 / 2 : ℝ) < (c - (r : ℂ)).re := (dottieScaledRightDisk_strip hl).1
  have hright : (c + (r : ℂ)).re < (1 : ℝ) := (dottieScaledRightDisk_strip hu).2
  rw [sub_re, ofReal_re] at hleft
  rw [add_re, ofReal_re] at hright
  constructor
  · exact (show r < c.re by linarith).trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm c))
  · have h : r < (1 - c).re := by rw [sub_re, one_re]; linarith
    exact h.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm (1 - c)))

/-- A signed enclosure at each rational sample covers the whole Dottie
circumference after paying for input variation and the Mellin tail once. -/
theorem dottie_completed_boundary_of_rational_samples
    (K : Type) [Field K] [NumberField K] (R : ℝ) (hR : 1 ≤ R)
    {T margin tail : ℝ} {n m : ℕ} (hm : 0 < m) (axis : ℂ) (haxis : ‖axis‖ = 1)
    (hTail : 2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      ≤ tail)
    (hSamples : ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      (axis * mixedThetaCompletedTruncation K R
        (rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j)).im +
          mixedThetaContourVariation K R (dottieScaledRightCenter T n) (dottieScaledRadius n) *
            (2 * dottieScaledRadius n / (m : ℝ)) + tail ≤ -margin) :
    ∀ w ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (axis * mixedThetaCompletedReading K w).im ≤ -margin := by
  intro w hw
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  let V := mixedThetaContourVariation K R c r
  have hr : 0 < r := by dsimp [r, dottieScaledRadius, dottieRingScale]; positivity
  have hV : 0 ≤ V := by
    have hMass : 0 ≤ ∫ t : ℝ in 1..R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ :=
      intervalIntegral.integral_nonneg hR (fun _ _ => norm_nonneg _)
    have hLog := Real.log_nonneg hR
    change 0 ≤ mixedThetaContourVariation K R c r
    unfold mixedThetaContourVariation contourPoleVariation
    positivity
  obtain ⟨a, ha, j, hj, hnear⟩ := exists_near_rationalContourSample hr hw hm
  let v := rationalContourSample c r a m j
  have hwD := Metric.sphere_subset_closedBall hw
  have hvD : v ∈ Metric.closedBall c r :=
    Metric.sphere_subset_closedBall (rationalContourSample_mem_sphere hr ha)
  have hwS := dottieScaledRightDisk_strip hwD
  have hvS := dottieScaledRightDisk_strip hvD
  have hw₀ : 0 < w.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hwS.1
  have hv₀ : 0 < v.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hvS.1
  obtain ⟨hc, hc1⟩ := dottie_closedBall_avoids_poles T n
  have hosc := mixedThetaCompletedTruncation_difference_le_on_disk K hR hc hc1 hwD hvD
    hw₀.le hwS.2.le hv₀.le hvS.2.le
  have hdelta : ‖mixedThetaCompletedTruncation K R w - mixedThetaCompletedTruncation K R v‖ ≤
      V * (2 * r / (m : ℝ)) := by
    exact hosc.trans (mul_le_mul_of_nonneg_left ((dist_eq_norm w v) ▸ hnear) hV)
  have hSigned := mixedThetaCompletedReading_im_le_of_truncation K R hR axis w haxis hw₀ hwS.2
  have hSignedDiff : (axis * (mixedThetaCompletedTruncation K R w -
      mixedThetaCompletedTruncation K R v)).im ≤ V * (2 * r / (m : ℝ)) := by
    refine (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans ?_)
    simpa only [norm_mul, haxis, one_mul] using hdelta
  rw [mul_sub, sub_im] at hSignedDiff
  have hs := hSamples a ha j hj
  change (axis * mixedThetaCompletedTruncation K R v).im + V * (2 * r / (m : ℝ)) + tail
    ≤ -margin at hs
  linarith only [hSigned, hSignedDiff, hTail, hs]

#print axioms contourPoleDifference_le
#print axioms mixedThetaCompletedTruncation_difference_le_on_disk
#print axioms dottie_completed_boundary_of_rational_samples

end

end FieldTarget
