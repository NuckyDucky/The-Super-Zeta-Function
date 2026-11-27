import DedekindMixedThetaSampleCover
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace FieldTarget

open Complex Filter MeasureTheory Set SuperZeta.StirlingCorrection
open DedekindZetaZeroFree.AbelianQuotient
open scoped Topology

private theorem dottie_boundary_unit_axis {F : ℂ → ℂ} {T : ℝ} {n : ℕ}
    (h : HasDottieBoundarySign F T n) :
    ∃ axis : ℂ, ‖axis‖ = 1 ∧ ∃ margin : ℝ, 0 < margin ∧
      ∀ w ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
        (axis * F w).im ≤ -margin := by
  obtain ⟨a, δ, hδ, hsign⟩ := h
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hz : c + (r : ℂ) ∈ Metric.sphere c r := by
    rw [Metric.mem_sphere, dist_eq_norm, show c + (r : ℂ) - c = (r : ℂ) by ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have ha : a ≠ 0 := by
    intro ha0
    have hzero : (0 : ℝ) ≤ -δ := by simpa [ha0] using hsign (c + (r : ℂ)) hz
    linarith only [hzero, hδ]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ℂ := ((‖a‖⁻¹ : ℝ) : ℂ) * a
  have hb : ‖b‖ = 1 := by
    dsimp only [b]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  refine ⟨b, hb, ‖a‖⁻¹ * δ, mul_pos (inv_pos.mpr hn) hδ, fun w hw => ?_⟩
  calc
    (b * F w).im = ‖a‖⁻¹ * (a * F w).im := by
      dsimp only [b]
      rw [mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    _ ≤ ‖a‖⁻¹ * (-δ) := mul_le_mul_of_nonneg_left (hsign w hw) (inv_nonneg.mpr hn.le)
    _ = -(‖a‖⁻¹ * δ) := mul_neg _ _

/-- Every strict disk sign is detected by some finite truncation and rational mesh. -/
theorem dottie_completed_samples_iff_boundary_sign (K : Type) [Field K] [NumberField K]
    (T : ℝ) (n : ℕ) :
    HasDottieCompletedSamples K T n ↔ HasDottieBoundarySign (mixedThetaCompletedReading K) T n := by
  constructor
  · rintro ⟨R, hR, m, hm, axis, haxis, margin, hmargin, tail, hTail, hSamples⟩
    exact ⟨axis, margin, hmargin,
      dottie_completed_boundary_of_rational_samples K R hR hm axis haxis hTail hSamples⟩
  · intro hsign
    obtain ⟨axis, haxis, δ, hδ, hsgn⟩ := dottie_boundary_unit_axis hsign
    let c := dottieScaledRightCenter T n
    let r := dottieScaledRadius n
    let tail (R : ℝ) :=
      2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
    have hlim : Tendsto tail atTop (𝓝 0) := by
      have h := tendsto_integral_Ioi_zero
        (f := fun t : ℝ => ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖)
        (μ := volume) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
      simpa only [tail, id_eq, mul_zero] using h.const_mul (2 : ℝ)
    have hδq : 0 < δ/4 := by positivity
    have hsmall : ∀ᶠ R in atTop, tail R < δ/4 :=
      hlim.eventually (gt_mem_nhds hδq)
    obtain ⟨R, hR, hTail⟩ := ((eventually_ge_atTop (1 : ℝ)).and hsmall).exists
    let V := mixedThetaContourVariation K R c r
    obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (V * (2*r) / (δ/4)))
    have hm' : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
    have hmul : V * (2*r) < (m : ℝ) * (δ/4) :=
      (div_lt_iff₀ hδq).mp ((le_max_right _ _).trans_lt hm)
    have hV : V * (2*r/(m : ℝ)) ≤ δ/4 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hm').mpr (by simpa only [mul_comm (m : ℝ) (δ/4)] using hmul.le)
    refine ⟨R, hR, m, by exact_mod_cast hm', axis, haxis, δ/4, hδq, δ/4, hTail.le, ?_⟩
    intro a ha j _
    let w := rationalContourSample c r a m j
    have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
    have hw : w ∈ Metric.sphere c r := rationalContourSample_mem_sphere hr ha
    have hstrip := dottieScaledRightDisk_strip (Metric.sphere_subset_closedBall hw)
    have herr := mixedThetaCompletedTruncation_error_le K R hR w
      ((by norm_num : (0 : ℝ) < 1/2).trans hstrip.1) hstrip.2
    have hdiff : (axis * (mixedThetaCompletedTruncation K R w -
        mixedThetaCompletedReading K w)).im ≤ δ/4 := by
      calc
        _ ≤ ‖axis * (mixedThetaCompletedTruncation K R w - mixedThetaCompletedReading K w)‖ :=
          (le_abs_self _).trans (Complex.abs_im_le_norm _)
        _ = ‖mixedThetaCompletedReading K w - mixedThetaCompletedTruncation K R w‖ := by
          rw [norm_mul, haxis, one_mul, norm_sub_rev]
        _ ≤ δ/4 := herr.trans hTail.le
    rw [mul_sub, Complex.sub_im] at hdiff
    have hwSign := hsgn w hw
    change (axis * mixedThetaCompletedTruncation K R w).im + V * (2*r/(m : ℝ)) + δ/4 ≤ -(δ/4)
    linarith only [hdiff, hwSign, hV]

/-- The very same disks can be certified by a boundary sign or by finite samples. -/
theorem finite_dottie_boundary_iff_completed_sample_cover (K : Type) [Field K] [NumberField K]
    (l u : ℝ) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K) l u ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ disks : Finset (DottieBandRing l u),
        (∀ w : ℂ, w.im ∈ Icc l u → 1/2 < w.re → w.re ≤ 31/32 →
          w.re - 1/2 < ε → mixedThetaContinuation K w ≠ 0) ∧
        (∀ w : ℂ, w.im ∈ Icc l u → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
          ∃ a ∈ disks, w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2)
            (dottieScaledRadius a.val.2)) ∧
        ∀ a ∈ disks, HasDottieCompletedSamples K a.val.1 a.val.2 := by
  constructor
  · rintro ⟨ε, hε, disks, hclear, hcover, hsign⟩
    exact ⟨ε, hε, disks, hclear, hcover, fun a ha =>
      (dottie_completed_samples_iff_boundary_sign K a.val.1 a.val.2).mpr (hsign a ha)⟩
  · rintro ⟨ε, hε, disks, hclear, hcover, hsample⟩
    exact ⟨ε, hε, disks, hclear, hcover, fun a ha =>
      (dottie_completed_samples_iff_boundary_sign K a.val.1 a.val.2).mp (hsample a ha)⟩

#check @dottie_completed_samples_iff_boundary_sign
#check @finite_dottie_boundary_iff_completed_sample_cover
#print axioms dottie_completed_samples_iff_boundary_sign
#print axioms finite_dottie_boundary_iff_completed_sample_cover

end FieldTarget
