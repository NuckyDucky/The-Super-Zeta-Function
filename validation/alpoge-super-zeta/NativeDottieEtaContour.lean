import MellinFixedAssembly
import NativeDottieFactorContours

/-! Transfer a local eta certificate to the original ordered cross-product. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Filter Metric Set
open scoped Topology

def etaFactor (s : ℂ) : ℂ := 1 - (2:ℂ) ^ (1 - 2*s)

def doubledEta (s : ℂ) : ℂ := etaFactor s * doubledZeta s

theorem etaFactor_ne_zero {s : ℂ} (hs : s ∈ openSpectralStrip) : etaFactor s ≠ 0 := by
  have hr : 0 < (1 - 2*s).re := by
    have h : s.re < (1:ℝ)/2 := hs.2
    simp only [sub_re, one_re, show ((2:ℂ)*s).re = 2*s.re by simp]
    linarith
  have hn : 1 < ‖(2:ℂ) ^ (1-2*s)‖ := by
    change 1 < ‖((2:ℝ):ℂ) ^ (1-2*s)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
    exact Real.one_lt_rpow (by norm_num) hr
  intro hz
  have hh : (1:ℂ) = (2:ℂ) ^ (1 - 2*s) := sub_eq_zero.mp hz
  rw [← hh, norm_one] at hn
  exact (lt_irrefl (1:ℝ)) hn

private theorem etaFactor_diff : Differentiable ℂ etaFactor := by
  unfold etaFactor
  simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
  fun_prop

private theorem thirdFactor_entire : Differentiable ℂ thirdFactor := by
  unfold thirdFactor
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
  fun_prop

theorem doubledEta_diff_on_strip : DifferentiableOn ℂ doubledEta openSpectralStrip := by
  refine etaFactor_diff.differentiableOn.mul ?_
  intro s hs
  exact ((SuperZeta.Multiplicity.analytic_zeta
    (SuperZeta.Multiplicity.doubled_ne_pole hs.2)).comp
    (SuperZeta.Multiplicity.scale_analytic 2 s)).differentiableAt.differentiableWithinAt

/-- The two numerical tests may be made on the eta factor. The count and
weighted location are still read on the original Dottie cross-product. -/
theorem firstContour_read_of_eta
    (hgap : ∀ s ∈ closedBall firstCenter firstRadius, correctionGap s ≠ 0)
    {a : ℂ} (ha : a ≠ 0)
    (hcenter : ‖doubledEta firstCenter / a‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ closedBall firstCenter firstRadius,
      ‖1 - deriv doubledEta s / a‖ ≤ 1/4) :
    ∃ ρ ∈ ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius nativeCross p = p ρ) := by
  let unit (s : ℂ) := correctionGap s * thirdFactor s / etaFactor s
  have hUdiff : DifferentiableOn ℂ unit openSpectralStrip :=
    (correctionGap_entire.mul thirdFactor_entire).differentiableOn.div
      etaFactor_diff.differentiableOn (fun _ hs => etaFactor_ne_zero hs)
  have hUnz (s : ℂ) (hs : s ∈ closedBall firstCenter firstRadius) : unit s ≠ 0 :=
    div_ne_zero (mul_ne_zero (hgap s hs) (thirdFactor_ne_zero (firstDisk_in_strip hs).1))
      (etaFactor_ne_zero (firstDisk_in_strip hs))
  have hEq (s : ℂ) (hs : s ∈ openSpectralStrip) : nativeCross s = unit s * doubledEta s := by
    rw [native_cross_eq, sharedReference_eq (SuperZeta.Multiplicity.doubled_ne_pole hs.2)]
    simp only [unit, doubledEta, doubledZeta, div_eq_mul_inv]
    rw [mul_assoc _ (etaFactor s)⁻¹, ← mul_assoc (etaFactor s)⁻¹,
      inv_mul_cancel₀ (etaFactor_ne_zero hs), one_mul, mul_assoc]
    rfl
  have hCdiff : DifferentiableOn ℂ nativeCross openSpectralStrip :=
    (hUdiff.mul doubledEta_diff_on_strip).congr hEq
  have hFdiff (s : ℂ) (hs : s ∈ openSpectralStrip) : DifferentiableAt ℂ doubledEta s :=
    doubledEta_diff_on_strip.differentiableAt (openSpectralStrip_open.mem_nhds hs)
  have hc : ‖doubledEta firstCenter / a‖ < (3/4)*firstRadius :=
    lt_of_le_of_lt hcenter (by norm_num)
  obtain ⟨ρ,hρ,hzero,hderiv,hunique⟩ := unique_simple_zero_of_defect
    (by norm_num) ha (fun _ hs => hFdiff _ (firstDisk_in_strip hs)) hc hdefect
  have hρD := ball_subset_closedBall hρ
  have hρS := firstDisk_in_strip hρD
  have hC0 : nativeCross ρ = 0 := by rw [hEq ρ hρS, hzero, mul_zero]
  have hCder : deriv nativeCross ρ ≠ 0 := by
    have he : nativeCross =ᶠ[𝓝 ρ] fun s => unit s * doubledEta s := by
      filter_upwards [openSpectralStrip_open.mem_nhds hρS] with s hs
      exact hEq s hs
    rw [he.deriv_eq, deriv_mul (hUdiff.differentiableAt
      (openSpectralStrip_open.mem_nhds hρS)) (hFdiff ρ hρS), hzero, mul_zero, zero_add]
    exact mul_ne_zero (hUnz ρ hρD) hderiv
  have hZ : riemannZeta (2*ρ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (etaFactor_ne_zero hρS)
  have hCunique (s : ℂ) (hs : s ∈ closedBall firstCenter firstRadius)
      (hz : nativeCross s = 0) : s = ρ := by
    rw [hEq s (firstDisk_in_strip hs)] at hz
    exact hunique s hs ((mul_eq_zero.mp hz).resolve_left (hUnz s hs))
  refine ⟨ρ, hρ, hC0, hCder, hZ, (fun s hs => ⟨hCunique s hs, ?_⟩), ?_⟩
  · intro he
    rw [he]
    exact hC0
  · intro p hp
    exact weightedCircle_of_simple_root openSpectralStrip_open firstDisk_in_strip
      hCdiff hp hρ hC0 hCder hCunique

theorem firstContour_read_of_checked_range_and_eta
    (h : MellinFixed.checkTableRange 576 1728 = true)
    {a : ℂ} (ha : a ≠ 0)
    (hcenter : ‖doubledEta firstCenter / a‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ closedBall firstCenter firstRadius,
      ‖1 - deriv doubledEta s / a‖ ≤ 1/4) :
    ∃ ρ ∈ ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius nativeCross p = p ρ) := by
  refine firstContour_read_of_eta ?_ ha hcenter hdefect
  intro s hs hzero
  have hgap := MellinFixed.firstDisk_correctionGap_of_checked_range h hs
  norm_num [hzero] at hgap

#print axioms doubledEta_diff_on_strip
#print axioms firstContour_read_of_eta
#print axioms firstContour_read_of_checked_range_and_eta

end DottieOriented.NativeSpectrum
end
