import NativeDottieGapDisk
import NativeDottieFactorContours

/-! The first native Dottie contour is centered on the reflection line.
A unique zero on this disk must be fixed by reflection. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex MeasureTheory Set Metric
open scoped Real ComplexConjugate

private theorem cpow_conj_real {x : ℝ} (hx : 0 ≤ x) (w : ℂ) :
    conj ((x : ℂ)^w) = (x : ℂ)^(conj w) := by
  have h := Complex.conj_cpow (x : ℂ) (conj w)
    (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)
  simpa only [Complex.conj_conj, Complex.conj_ofReal] using h.symm

private theorem modifiedTheta_conj (t : ℝ) :
    conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := by
  by_cases h₁ : t ∈ Ioi (1:ℝ) <;> by_cases h₂ : t ∈ Ioo (0:ℝ) 1 <;>
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, Set.indicator_apply,
      h₁, h₂, smul_eq_mul]

private theorem completedZeta_conj (w : ℂ) :
    completedRiemannZeta (conj w) = conj (completedRiemannZeta w) := by
  have h₀ : completedRiemannZeta₀ (conj w) = conj (completedRiemannZeta₀ w) := by
    change mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (conj w/2)/2 =
      conj (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (w/2)/2)
    rw [map_div₀, map_ofNat]
    congr 1
    unfold mellin
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, map_mul, modifiedTheta_conj,
      cpow_conj_real (mem_Ioi.mp ht).le, map_sub, map_div₀, map_one, map_ofNat]
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, map_sub, map_sub, h₀]
  simp only [map_div₀, map_one, map_sub]

private theorem doubled_zero_reflects {s : ℂ} (hs : s ∈ openSpectralStrip)
    (hz : doubledZeta s = 0) : doubledZeta (1/2-conj s) = 0 := by
  have h₀ : 0 < (2*s).re := by simp only [two_mul, add_re]; linarith [hs.1]
  have hn : (2*s) ≠ 0 := by
    intro he
    simp [he] at h₀
  have href : 2*(1/2-conj s) = 1-conj (2*s) := by rw [map_mul, map_ofNat]; ring
  have hr : 0 < (1-conj (2*s)).re := by
    simp only [sub_re, one_re, conj_re, two_mul, add_re]
    linarith [hs.2]
  have hrn : 1-conj (2*s) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [zero_re] at h
    linarith only [hr, h]
  unfold doubledZeta at hz ⊢
  rw [riemannZeta_def_of_ne_zero hn] at hz
  have hc := (div_eq_zero_iff.mp hz).resolve_right (Gammaℝ_ne_zero_of_re_pos h₀)
  rw [href, riemannZeta_def_of_ne_zero hrn, completedRiemannZeta_one_sub,
    completedZeta_conj, hc, map_zero, zero_div]

theorem firstDisk_reflects {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    1/2-conj s ∈ closedBall firstCenter firstRadius := by
  have h : 1/2-conj s-firstCenter = -conj (s-firstCenter) := by
    apply Complex.ext
    · simp only [sub_re, div_ofNat_re, one_re, conj_re, neg_re, firstCenter]
      ring
    · norm_num [firstCenter, Complex.sub_im, Complex.div_ofNat_im]
      ring
  simpa only [mem_closedBall, dist_eq_norm, h, norm_neg, norm_conj] using hs

/-- The zero recovered by the centered first contour moment has real part
exactly one quarter. The numerical inputs are the centered Mellin enclosures
and contraction bounds of the first disk. -/
theorem firstContour_on_line
    (hzero : (1188:ℝ)/10^9 ≤ ‖centerCoefficient 0‖)
    (hhigh : ∀ k : ℕ, 0 < k → k < 4 → ‖centerCoefficient k‖ ≤ (5:ℝ)/10^6)
    (hcenter : ‖nativeCross firstCenter / firstDirection‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ closedBall firstCenter firstRadius,
      ‖1 - deriv nativeCross s / firstDirection‖ ≤ 1/4) :
    firstContourPoint.re = 1/4 ∧
    weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
    riemannZeta (2*firstContourPoint) = 0 ∧
    (∀ s ∈ closedBall firstCenter firstRadius,
      riemannZeta (2*s) = 0 ↔ s = firstContourPoint) := by
  obtain ⟨-, hcount, hball, -, -, hz, huniq⟩ :=
    firstContour_taylor_certificate hzero hhigh hcenter hdefect
  have heq {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
      nativeCross s = 0 ↔ riemannZeta (2*s) = 0 := by
    have hd := firstDisk_in_strip hs
    apply native_cross_zero_iff hd.1 hd.2
    intro he
    exact gap_ne_zero_from_center_coefficients hzero hhigh hs (sub_eq_zero.mpr he)
  have hm := firstDisk_reflects (ball_subset_closedBall hball)
  have href := doubled_zero_reflects (firstDisk_in_strip (ball_subset_closedBall hball)) hz
  have hfix := huniq _ hm ((heq hm).mpr href)
  have hreal := congrArg Complex.re hfix
  simp only [sub_re, div_ofNat_re, one_re, conj_re] at hreal
  refine ⟨by linarith, hcount, hz, fun s hs => ⟨fun h => huniq s hs ((heq hs).mpr h), ?_⟩⟩
  intro h
  rwa [h]

#print axioms firstDisk_reflects
#print axioms firstContour_on_line
#check firstContour_on_line

end DottieOriented.NativeSpectrum
end
