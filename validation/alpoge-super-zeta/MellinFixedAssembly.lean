import MellinFixedRanges
import MellinFixedTableSound
import MellinIntegerCertificate

/-! The exact end-to-end implication from the full table replay to the correction gap. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

open MellinInteger

theorem firstDisk_correctionGap_of_checked_range
    (h : checkTableRange 576 1728 = true)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600 : ℝ) < ‖correctionGap s‖ := by
  refine firstDisk_correctionGap_from_middle_samples ?_ hs
  intro b i hi hj j
  have hm : i ∈ List.range' 576 1728 := (List.mem_range'_1).mpr ⟨hi,hj⟩
  exact checkTablePanel_correct hi hj (List.all_eq_true.mp h i hm) b j

theorem firstContour_read_of_checked_range
    (h : checkTableRange 576 1728 = true)
    (hcenter : ‖nativeCross firstCenter / firstDirection‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ Metric.closedBall firstCenter firstRadius,
      ‖1 - deriv nativeCross s / firstDirection‖ ≤ 1/4) :
    ∃ ρ ∈ Metric.ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ Metric.closedBall firstCenter firstRadius, nativeCross s = 0 → s = ρ) ∧
      weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
      firstContourPoint = ρ := by
  refine firstContour_read ?_ hcenter hdefect
  intro s hs hz
  have hgap := firstDisk_correctionGap_of_checked_range h hs
  norm_num [hz] at hgap

#print axioms firstDisk_correctionGap_of_checked_range
#print axioms firstContour_read_of_checked_range

end DottieOriented.NativeSpectrum.MellinFixed
end
