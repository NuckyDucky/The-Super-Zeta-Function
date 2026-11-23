import ArchivedDottieHeight
import ArchivedQuarticZeroTransport

/-! The fixed ring addresses and signed boundary test in the normalization
of the archived Gaussian circle calculation. -/

open Complex Set
open scoped ComplexConjugate

namespace QuarticModel

open SuperZeta.StirlingCorrection

noncomputable def archivedDottieRightRing : Set ℂ :=
  {w | 15/1024 < dist w (archivedRightCenter dottieHeight) ∧
    dist w (archivedRightCenter dottieHeight) < 31/2048}

theorem archivedDottieRing_address {w : ℂ}
    (hw : w ∈ archivedDottieRightRing) :
    (15/64 : ℝ) ≤ (w/2).re ∧ (w/2).re ≤ 17/64 ∧ 101 ≤ (w/2).im := by
  have hdist : dist w (archivedRightCenter dottieHeight) ≤ 31/2048 := hw.2.le
  rw [dist_eq_norm] at hdist
  have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hdist)
  have him := abs_le.mp ((Complex.abs_im_le_norm _).trans hdist)
  change -(31/2048 : ℝ) ≤ w.re - 33/64 ∧ w.re - 33/64 ≤ 31/2048 at hre
  change -(31/2048 : ℝ) ≤ w.im - (dottieHeight-1/512) ∧
    w.im - (dottieHeight-1/512) ≤ 31/2048 at him
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im]
  exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1, dottieHeight_enclosure.1]⟩

/-- The circle replay divides by a positive completion scale before comparing
with the reference value. Convert those units in Lean at the original height. -/
theorem archivedDottieRing_exclusion_of_normalized_remainder
    {A S : ℝ} (hA : 0 < A) (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (H w).im ≤ -(190*((w.re-1/2)*S)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (archivedMellin w / (A : ℂ)-H w).im ≤ 189*((w.re-1/2)*S))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    (archivedMellin w).im ≤ -(A*S/2048) ∧
      A*S/2048 ≤ (archivedMellin (1-conj w)).im ∧ archivedGaussianFactor w ≠ 0 := by
  let G := fun z => (A : ℂ) * H z
  have hm : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (G z).im ≤ -(190*((z.re-1/2)*(A*S))) := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left (model z hz) hA.le
    simpa only [G, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] using
      (show A * (H z).im ≤ -(190*((z.re-1/2)*(A*S))) by linarith)
  have ht : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (archivedMellin z-G z).im ≤ 189*((z.re-1/2)*(A*S)) := by
    intro z hz
    have hne : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    have he : archivedMellin z - G z = (A : ℂ)*(archivedMellin z/(A : ℂ)-H z) := by
      dsimp [G]
      field_simp
    rw [he, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    have h := mul_le_mul_of_nonneg_left (tail z hz) hA.le
    linarith
  exact archivedRightDisk_exclusion_of_remainder (mul_pos hA hS) G hm ht
    (Metric.mem_closedBall.mpr hw.2.le)

noncomputable def archivedDottieCompletionScale : ℝ :=
  archivedThetaScale^2 * ‖Complex.Gamma (2+(dottieHeight : ℂ)*I)‖

theorem archivedDottieCompletionScale_pos : 0 < archivedDottieCompletionScale := by
  unfold archivedDottieCompletionScale
  apply mul_pos (pow_pos archivedThetaScale_pos _)
  exact norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))

/-- The exact signed test for the fixed Dottie ring, with the completion scale
used in both halves of the archived contour sum. -/
theorem archivedDottieRing_zero_free_of_replay
    {S : ℝ} (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (H w).im ≤ -(190*((w.re-1/2)*S)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (archivedMellin w / (archivedDottieCompletionScale : ℂ)-H w).im ≤ 189*((w.re-1/2)*S))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1-conj w) ≠ 0 := by
  have hh := archivedDottieRing_exclusion_of_normalized_remainder
    archivedDottieCompletionScale_pos hS H model tail hw
  have hr : 0 < (1-conj w).re := by
    simp only [sub_re, one_re, conj_re]
    obtain ⟨_, hy, _⟩ := archivedDottieRing_address hw
    rw [Complex.div_ofNat_re] at hy
    linarith
  refine ⟨hh.2.2, ?_⟩
  intro hz
  have he := (archivedGaussianFactor_zero_iff_mellin hr).mp hz
  have hmargin := hh.2.1
  rw [he, Complex.zero_im] at hmargin
  exact (not_le_of_gt (div_pos (mul_pos archivedDottieCompletionScale_pos hS) (by norm_num))) hmargin

#print axioms archivedDottieRing_address
#print axioms archivedDottieRing_exclusion_of_normalized_remainder
#print axioms archivedDottieRing_zero_free_of_replay

end QuarticModel
