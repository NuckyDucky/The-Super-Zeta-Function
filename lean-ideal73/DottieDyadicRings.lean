import DottieDyadicGeometry
import DottieMarkedHeight

/-! Apply dyadic homotheties about the critical line at the selected Dottie
height. The height witnesses and the original point stay available separately. -/

namespace SuperZeta.StirlingCorrection

open Complex Function Set SuperZeta.Reciprocal
open scoped ComplexConjugate

noncomputable section

/-- The same height witnesses can nominate wider measuring disks. The disk
contains the original complex input, with a scale chosen from its real part. -/
theorem dottie_scaled_band_selects_marked_returns {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re ≤ 127 / 128)
    (him : w.im + 1 / 512 ∈ Icc (dottieHeight - 10^8) (dottieHeight + 10^8))
    (hmarked : ∀ x ∈ Icc (archivedDottieFlank - dottieFlankWidth)
        (archivedDottieFlank + dottieFlankWidth), ∀ right : Bool,
        ∃ P Q, MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right)) :
    ∃ x n, dottieHeightAtFlank x = w.im + 1 / 512 ∧
      w ∈ Metric.closedBall (dottieScaledRightCenter (dottieHeightAtFlank x) n) (dottieScaledRadius n) ∧
      ∀ right : Bool, ∃ P Q,
        MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right) ∧
        minimalPeriod (step (dottieWitnessLift right x)) (P, Q) = 640 := by
  let w₀ : ℂ := ⟨33 / 64, w.im⟩
  have hre : w₀.re ∈ Icc (1 / 2 + 1 / 2048) (1 / 2 + 63 / 2048) := by
    norm_num [w₀, mem_Icc]
  obtain ⟨x, hheight, _, hpair⟩ := dottie_band_selects_marked_returns hre him hmarked
  obtain ⟨n, hw⟩ := dottieScaledRightDisk_covers hlo hhi
  exact ⟨x, n, hheight, by rw [hheight]; exact hw, hpair⟩

#print axioms dottieScaledRightDisk_real_bounds
#print axioms dottieScaledRightDisk_strip
#print axioms dottieScaledRightDisk_covers
#print axioms dottieScaledRightDisk_reflect
#print axioms dottie_scaled_band_selects_marked_returns

end

end SuperZeta.StirlingCorrection

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open scoped ComplexConjugate

/-- With the retained and remainder bounds on the chosen circumference,
the same signed test excludes zeros of the actual quartic Gaussian factor
on the full scaled disk and its reflected partner. -/
theorem archivedScaledRightDisk_exclusion_of_remainder {T S : ℝ} {n : ℕ}
    (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (H z).im ≤ -(190 * ((z.re - 1 / 2) * S)))
    (tail : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (archivedMellin z - H z).im ≤ 189 * ((z.re - 1 / 2) * S))
    {w : ℂ} (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    (archivedMellin w).im ≤ -(dottieRingScale n * S / 2048) ∧
      dottieRingScale n * S / 2048 ≤ (archivedMellin (1 - conj w)).im ∧
      archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1 - conj w) ≠ 0 := by
  have hs := dottieRingScale_pos n
  have hr : 0 < dottieScaledRadius n := mul_pos (by norm_num) hs
  have hboundary : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (archivedMellin z).im ≤ -(dottieRingScale n * S / 2048) := by
    intro z hz
    have hgap := (dottieScaledRightDisk_real_bounds (Metric.sphere_subset_closedBall hz)).1
    have hscaled := mul_le_mul_of_nonneg_right hgap hS.le
    have htail := tail z hz
    rw [sub_im] at htail
    linarith [model z hz]
  have hright := archivedMellin_im_le_on_disk hr hboundary hw
  have hleft : dottieRingScale n * S / 2048 ≤ (archivedMellin (1 - conj w)).im := by
    rw [(archivedMellin_mirror_coordinates w).2]
    linarith
  have hmargin : 0 < dottieRingScale n * S / 2048 := div_pos (mul_pos hs hS) (by norm_num)
  obtain ⟨hRe, hRe'⟩ := dottieScaledRightDisk_strip hw
  have hMirrorRe : 0 < (1 - conj w).re := by simp; linarith
  refine ⟨hright, hleft, ?_, ?_⟩
  · intro hz
    rw [(archivedGaussianFactor_zero_iff_mellin (by linarith : 0 < w.re)).mp hz, zero_im] at hright
    linarith
  · intro hz
    rw [(archivedGaussianFactor_zero_iff_mellin hMirrorRe).mp hz, zero_im] at hleft
    linarith

#print axioms archivedScaledRightDisk_exclusion_of_remainder

end QuarticModel
