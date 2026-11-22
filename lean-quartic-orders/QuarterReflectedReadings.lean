import QuartetDominance
import QuartetBandDominance
import QuartetBandCauchy
import QuarterHorizontal
import QuarterGaussianContrast
import SuperZeta.GaussianDiskCount

noncomputable section
namespace SuperZeta.QuarterReflectedReadings
open Complex UnitSpectrum QuarterHorizontal Set
open scoped ComplexConjugate

theorem outer_bound : QuartetBandCauchy.OuterBound :=
  fun _ hl hr ht => (QuartetBandDominance.band_relative_error hl hr ht).le

/-- The entire horizontal segment at each such height has strictly decreasing spectral modulus. -/
theorem decreasing {t : ℝ} (ht : 101 ≤ t) :
    StrictAntiOn (fun x => ‖continuation (atHeight t x)‖) (Icc (15/64:ℝ) (17/64)) := by
  apply norm_strictAnti
  · intro x _
    apply QuartetBandCauchy.continuation_diff
    simpa [atHeight] using (show 0 < t by linarith)
  · intro x hx
    have him : (atHeight t x).im = t := by simp [atHeight]
    have hre : (atHeight t x).re = x := by simp [atHeight]
    have hs := QuartetBandCauchy.log_slope (s:=atHeight t x) outer_bound
      (by rw [hre,abs_le]; constructor <;> linarith [hx.1,hx.2]) (him.symm ▸ ht)
    linarith

def left (t a : ℝ) := atHeight t (1/4-a)
def right (t a : ℝ) := atHeight t (1/4+a)

theorem reflected_order {a t : ℝ} (ha : 0 < a) (hb : a ≤ 1/64) (ht : 101 ≤ t) :
    0 < ‖continuation (right t a)‖ ∧ ‖continuation (right t a)‖ < ‖continuation (left t a)‖ := by
  constructor
  · apply norm_pos_iff.mpr
    apply QuartetBandCauchy.continuation_ne outer_bound
    · simpa [right,atHeight,abs_of_pos ha] using hb
    · simpa [right,atHeight] using ht
  · apply decreasing ht (show 1/4-a ∈ Icc (15/64:ℝ) (17/64) from ⟨by linarith,by linarith⟩)
      (show 1/4+a ∈ Icc (15/64:ℝ) (17/64) from ⟨by linarith,by linarith⟩)
    linarith

/-- If both reflected Riemann inputs are zeros, the Mellin correction must reproduce
the strictly ordered pair of nonzero original spectral readings. -/
theorem correction_order_at_two_zeros {a t : ℝ} (ha : 0 < a) (hb : a ≤ 1/64) (ht : 101 ≤ t)
    (hl : riemannZeta (2*left t a) = 0) (hr : riemannZeta (2*right t a) = 0) :
    0 < ‖Reference.entireCorrection 1 (right t a)‖ ∧
    ‖Reference.entireCorrection 1 (right t a)‖ < ‖Reference.entireCorrection 1 (left t a)‖ := by
  have zl : continuation (left t a) = Reference.entireCorrection 1 (left t a) := by
    simp [continuation,hl]
  have zr : continuation (right t a) = Reference.entireCorrection 1 (right t a) := by
    simp [continuation,hr]
  simpa only [←zl,←zr] using reflected_order ha hb ht

/-- The 31/2048 radius includes the outer measuring circle and its interior. -/
theorem right_disk_coordinates {w : ℂ} {T : ℝ} (ht : 203 ≤ T)
    (hw : w ∈ Metric.closedBall (GaussianDiskCount.rightCenter T) (31/2048)) :
    0 < (w.re-1/2)/2 ∧ (w.re-1/2)/2 ≤ 1/64 ∧ 101 ≤ w.im/2 := by
  change ‖w-GaussianDiskCount.rightCenter T‖ ≤ 31/2048 at hw
  have r := abs_le.mp ((Complex.abs_re_le_norm _).trans hw)
  have h := abs_le.mp ((Complex.abs_im_le_norm _).trans hw)
  simp only [sub_re,sub_im,GaussianDiskCount.rightCenter] at r h
  exact ⟨by linarith [r.1],by linarith [r.2],by linarith [h.1]⟩

theorem disk_spectral_order {w : ℂ} {T : ℝ} (ht : 203 ≤ T)
    (hw : w ∈ Metric.closedBall (GaussianDiskCount.rightCenter T) (31/2048)) :
    0 < ‖continuation (w/2)‖ ∧
      ‖continuation (w/2)‖ < ‖continuation ((1-conj w)/2)‖ := by
  obtain ⟨ha,hb,ht'⟩ := right_disk_coordinates ht hw
  have r : right (w.im/2) ((w.re-1/2)/2) = w/2 := by
    apply Complex.ext <;> simp [right,atHeight, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  have l : left (w.im/2) ((w.re-1/2)/2) = (1-conj w)/2 := by
    apply Complex.ext <;> simp [left,atHeight,Complex.div_ofNat_re,Complex.div_ofNat_im]
    ring
  simpa only [r,l] using reflected_order ha hb ht'

/-- This comparison requires only equality of the completed numerator magnitudes under reflection. -/
theorem gaussian_disk_contrast_iff {G : ℂ → ℂ} {w : ℂ} {T : ℝ} (ht : 203 ≤ T)
    (hw : w ∈ Metric.closedBall (GaussianDiskCount.rightCenter T) (31/2048))
    (href : ‖G w‖ = ‖G (1-conj w)‖) :
    0 < ‖G w / continuation (w/2)‖ - ‖G (1-conj w) / continuation ((1-conj w)/2)‖
      ↔ G w ≠ 0 := by
  obtain ⟨hr,ho⟩ := disk_spectral_order ht hw
  exact QuarterGaussianContrast.contrast_pos_iff href hr ho

end SuperZeta.QuarterReflectedReadings
