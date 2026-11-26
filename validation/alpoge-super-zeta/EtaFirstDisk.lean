import EtaCenterCertificate
import NativeDottieFirstLine

/-! The closed eta calculation determines the first zero and its weighted moments. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Metric Set
open scoped ComplexConjugate

open private doubled_zero_reflects from NativeDottieFirstLine

theorem eta_first_disk_certificate :
    ∃ ρ ∈ ball firstCenter firstRadius,
      ρ.re = 1/4 ∧ riemannZeta (2*ρ) = 0 ∧ deriv doubledEta ρ ≠ 0 ∧
      ‖ρ-firstCenter‖ ≤ (4:ℝ)/(3*10^6) ∧
      (∀ s ∈ closedBall firstCenter firstRadius, riemannZeta (2*s) = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius doubledEta p = p ρ) := by
  obtain ⟨ha,hcenter,hdefect⟩ :=
    eta_contour_inputs_of_finite_center MellinFixed.eta_center_bounds.1 MellinFixed.eta_center_bounds.2
  have hDiff (s : ℂ) (hs : s ∈ closedBall firstCenter firstRadius) :
      DifferentiableAt ℂ doubledEta s :=
    doubledEta_diff_on_strip.differentiableAt (openSpectralStrip_open.mem_nhds (firstDisk_in_strip hs))
  have hc : ‖doubledEta firstCenter / etaDiskDirection‖ < (3/4)*firstRadius :=
    lt_of_le_of_lt hcenter (by norm_num)
  obtain ⟨ρ,hρ,hz,hder,huniq⟩ :=
    unique_simple_zero_of_defect (by norm_num) ha hDiff hc hdefect
  have hρD := ball_subset_closedBall hρ
  have hZ : riemannZeta (2*ρ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (etaFactor_ne_zero (firstDisk_in_strip hρD))
  have hMirror := firstDisk_reflects hρD
  have hMirrorZ := doubled_zero_reflects (firstDisk_in_strip hρD) hZ
  have hMirrorEta : doubledEta (1/2-conj ρ) = 0 := by
    rw [doubledEta, hMirrorZ, mul_zero]
  have hFixed := congrArg Complex.re (huniq _ hMirror hMirrorEta)
  have hLine : ρ.re = 1/4 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.conj_re] at hFixed
    linarith
  let move (z : ℂ) : ℂ := z - doubledEta z / etaDiskDirection
  have hMove (z : ℂ) (hz' : z ∈ closedBall firstCenter firstRadius) :
      HasDerivAt move (1-deriv doubledEta z/etaDiskDirection) z :=
    (hasDerivAt_id z).sub ((hDiff z hz').hasDerivAt.div_const _)
  have hC : firstCenter ∈ closedBall firstCenter firstRadius := mem_closedBall_self (by norm_num)
  have hM := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz' => (hMove z hz').differentiableAt)
    (fun z hz' => by rw [(hMove z hz').deriv]; exact hdefect z hz')
    (convex_closedBall firstCenter firstRadius) hC hρD
  have hStay : move ρ = ρ := by simp only [move, hz, zero_div, sub_zero]
  have hAtCenter : move firstCenter-firstCenter = -(doubledEta firstCenter/etaDiskDirection) := by
    dsimp [move]
    ring
  have hR : ‖ρ-firstCenter‖ ≤ (4:ℝ)/(3*10^6) := by
    have h := norm_add_le (move ρ-move firstCenter) (move firstCenter-firstCenter)
    rw [sub_add_sub_cancel, hStay, hAtCenter, norm_neg] at h
    rw [hStay] at hM
    linarith only [h,hM,hcenter]
  refine ⟨ρ,hρ,hLine,hZ,hder,hR,?_,?_⟩
  · intro s hs
    constructor
    · intro hz'
      apply huniq s hs
      rw [doubledEta, doubledZeta, hz', mul_zero]
    · intro he
      simpa only [he] using hZ
  · intro p hp
    exact weightedCircle_of_simple_root openSpectralStrip_open firstDisk_in_strip
      doubledEta_diff_on_strip hp hρ hz hder huniq

theorem firstCross_root_certificate_of_replay
    (hsamples : MellinFixed.checkTableRange 576 1728 = true) :
    ∃ ρ ∈ ball firstCenter firstRadius,
      ρ.re = 1/4 ∧ riemannZeta (2*ρ) = 0 ∧
      ‖ρ-firstCenter‖ ≤ (4:ℝ)/(3*10^6) ∧
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧
      weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
      firstContourPoint = ρ := by
  obtain ⟨ρ,_,hRe,_,_,hR,hUniq,_⟩ := eta_first_disk_certificate
  obtain ⟨σ,hσ,hCross,hDer,hζ,_,hW⟩ := MellinFixed.firstContour_read_of_kernel_eta hsamples
  have hEq := (hUniq σ (ball_subset_closedBall hσ)).mp hζ
  subst σ
  refine ⟨ρ,hσ,hRe,hζ,hR,hCross,hDer,hW _ (differentiable_const _),?_⟩
  unfold firstContourPoint
  rw [hW (fun s : ℂ => s - firstCenter) (differentiable_id.sub_const firstCenter)]
  ring

#print axioms eta_first_disk_certificate
#print axioms firstCross_root_certificate_of_replay

end DottieOriented.NativeSpectrum
end
