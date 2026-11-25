import MellinMiddleAll
import EtaFirstDisk

/-! The first ordered Dottie contour with the saved Mellin table checked. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

theorem firstCross_disk_correctionGap {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600 : ℝ) < ‖correctionGap s‖ :=
  MellinFixed.firstDisk_correctionGap_of_checked_range MellinFixed.middle_samples_checked hs

theorem firstCross_disk_certificate :
    ∃ ρ ∈ Metric.ball firstCenter firstRadius,
      ρ.re = 1/4 ∧ riemannZeta (2*ρ) = 0 ∧
      ‖ρ-firstCenter‖ ≤ (4:ℝ)/(3*10^6) ∧
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧
      weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
      firstContourPoint = ρ ∧
      (∀ s ∈ Metric.closedBall firstCenter firstRadius, nativeCross s = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius nativeCross p = p ρ) := by
  obtain ⟨ρ,hρ,hRe,hζ,hDist,hCross,hDer,hCount,hPoint⟩ :=
    firstCross_root_certificate_of_replay MellinFixed.middle_samples_checked
  obtain ⟨σ,_,_,_,_,hUnique,hWeights⟩ :=
    MellinFixed.firstContour_read_of_kernel_eta MellinFixed.middle_samples_checked
  have hSame := (hUnique ρ (Metric.ball_subset_closedBall hρ)).mp hCross
  subst σ
  exact ⟨ρ,hρ,hRe,hζ,hDist,hCross,hDer,hCount,hPoint,hUnique,hWeights⟩

#check firstCross_disk_certificate
#print axioms firstCross_disk_correctionGap
#print axioms firstCross_disk_certificate

end DottieOriented.NativeSpectrum
end
