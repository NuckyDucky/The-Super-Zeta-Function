import NativeDottieContact
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.MetricSpace.Contracting

/-!
The simple-root case of Alpöge's weighted circle argument, applied to the
native Dottie cross-product. All numerical premises refer to the same disk.
-/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Metric Set Filter SuperZeta
open scoped Real NNReal Topology

def correctionGap (s : ℂ) : ℂ := correction false s - correction true s

theorem correctionGap_entire : Differentiable ℂ correctionGap :=
  (correction_entire false).sub (correction_entire true)

theorem cross_as_product : nativeCross = fun s => correctionGap s * sharedReference s :=
  funext native_cross_eq

def weightedCircle (c : ℂ) (r : ℝ) (f weight : ℂ → ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ z in C(c,r), weight z * logDeriv f z

private theorem circle_normalizer_ne_zero : (2 * π * I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

/-- Alpöge's weighted contour evaluation for one simple root. Dividing out
that root by dslope extends the quotient across the root itself. -/
theorem weightedCircle_of_simple_root {O : Set ℂ} {f p : ℂ → ℂ} {c a : ℂ} {r : ℝ}
    (hO : IsOpen O) (hD : closedBall c r ⊆ O) (hf : DifferentiableOn ℂ f O)
    (hp : Differentiable ℂ p) (ha : a ∈ ball c r) (hfa : f a = 0)
    (hda : deriv f a ≠ 0) (hunique : ∀ z ∈ closedBall c r, f z = 0 → z = a) :
    weightedCircle c r f p = p a := by
  let U := dslope f a
  have hr : 0 ≤ r := (dist_nonneg.trans_lt (mem_ball.mp ha)).le
  have hU : DifferentiableOn ℂ U O := (Complex.differentiableOn_dslope
    (hO.mem_nhds (hD (ball_subset_closedBall ha)))).mpr hf
  have fac (z : ℂ) : (z - a) * U z = f z := by
    simpa [U, smul_eq_mul, hfa] using sub_smul_dslope f a z
  have hU₀ (z : ℂ) (hz : z ∈ closedBall c r) : U z ≠ 0 := by
    intro h
    have hzfa := (fac z).symm.trans (by rw [h, mul_zero])
    have hz' := hunique z hz hzfa
    subst z
    exact hda (by simpa [U, dslope_same] using h)
  have hz₀ (z : ℂ) (hz : z ∈ sphere c r) : z - a ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro eq
    subst z
    exact (ne_of_lt (mem_ball.mp ha)) (mem_sphere.mp hz)
  let singular (z : ℂ) := (z-a)⁻¹ * p z
  let regular (z : ℂ) := p z * logDeriv U z
  have hreg (z : ℂ) (hz : z ∈ closedBall c r) : DifferentiableAt ℂ regular z := by
    have hzO := hO.mem_nhds (hD hz)
    exact (hp z).mul (((hU.deriv hO).differentiableAt hzO).div (hU.differentiableAt hzO) (hU₀ z hz))
  have hregc : ContinuousOn regular (closedBall c r) :=
    fun z hz => (hreg z hz).continuousAt.continuousWithinAt
  have hintreg : CircleIntegrable regular c r :=
    ContinuousOn.circleIntegrable hr (hregc.mono sphere_subset_closedBall)
  have hintsing : CircleIntegrable singular c r := by
    apply ContinuousOn.circleIntegrable hr
    exact ((continuous_id.sub continuous_const).continuousOn.inv₀ hz₀).mul hp.continuous.continuousOn
  have hreg0 : (∮ z in C(c,r), regular z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty hregc
      (fun z hz => hreg z (ball_subset_closedBall hz.1))
  have hsing : (∮ z in C(c,r), singular z) = (2 * π * I : ℂ) * p a := by
    simpa [singular, smul_eq_mul] using hp.differentiableOn.circleIntegral_sub_inv_smul ha
  have hsplit : Set.EqOn (fun z => p z * logDeriv f z) (singular + regular) (sphere c r) := by
    intro z hz
    have hlin : logDeriv (fun t : ℂ => t-a) z = (z-a)⁻¹ := by
      simp [logDeriv_apply, div_eq_mul_inv]
    have hd : DifferentiableAt ℂ (fun t : ℂ => t-a) z := differentiableAt_id.sub_const _
    have h := logDeriv_mul z (hz₀ z hz) (hU₀ z (sphere_subset_closedBall hz)) hd
      (hU.differentiableAt (hO.mem_nhds (hD (sphere_subset_closedBall hz))))
    rw [funext fac, hlin] at h
    simp only [Pi.add_apply, singular, regular, h]
    ring
  unfold weightedCircle
  rw [circleIntegral.integral_congr hr hsplit]
  simp only [Pi.add_apply]
  rw [circleIntegral.integral_add hintsing hintreg, hsing, hreg0, add_zero, ← mul_assoc,
    inv_mul_cancel₀ circle_normalizer_ne_zero, one_mul]

/-- A derivative bound on the disk and the residual at its center give an
interior zero and uniqueness on the closed disk. -/
theorem unique_simple_zero_of_defect {f : ℂ → ℂ} {c a : ℂ} {r : ℝ}
    (hr : 0 < r) (ha : a ≠ 0)
    (hf : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hc : ‖f c / a‖ < (3/4)*r)
    (hd : ∀ z ∈ closedBall c r, ‖1 - deriv f z / a‖ ≤ 1/4) :
    ∃ ρ ∈ ball c r, f ρ = 0 ∧ deriv f ρ ≠ 0 ∧
      ∀ z ∈ closedBall c r, f z = 0 → z = ρ := by
  let D := closedBall c r
  let g (z : ℂ) := z - f z / a
  have hcenter : c ∈ D := mem_closedBall_self hr.le
  have hG (z : ℂ) (hz : z ∈ D) : HasDerivAt g (1 - deriv f z / a) z := by
    simpa only [g, id_eq] using (hasDerivAt_id z).sub ((hf z hz).hasDerivAt.div_const a)
  have hL : LipschitzOnWith (1/4 : ℝ≥0) g D :=
    (convex_closedBall c r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hG z hz).hasDerivWithinAt) (fun z hz => by exact_mod_cast hd z hz)
  have hdist (x y : ℂ) (hx : x ∈ D) (hy : y ∈ D) : dist (g x) (g y) ≤ (1/4)*dist x y := by
    have h := (lipschitzWith_iff_dist_le_mul.mp hL.to_restrict) ⟨x,hx⟩ ⟨y,hy⟩
    simpa [D] using h
  have hmove : dist (g c) c < (3/4)*r := by
    simpa [g, dist_eq_norm, sub_sub_cancel_left] using hc
  have hinside (z : ℂ) (hz : z ∈ D) : g z ∈ ball c r := by
    rw [mem_ball]
    have hz' := mem_closedBall.mp hz
    linarith only [dist_triangle (g z) (g c) c, hdist z c hz hcenter, hmove, hz']
  have hmap : MapsTo g D D := fun z hz => ball_subset_closedBall (hinside z hz)
  have hcontract : ContractingWith (1/4 : ℝ≥0) (hmap.restrict g D D) :=
    ⟨by exact_mod_cast (by norm_num : (1/4 : ℝ) < 1), hL.to_restrict_mapsTo hmap⟩
  have hfix (z : ℂ) : g z = z ↔ f z = 0 := by
    simp [g, div_eq_zero_iff, ha]
  obtain ⟨ρ, hρ, hρfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hcenter (edist_ne_top _ _)
  have hρeq : g ρ = ρ := hρfix
  have hρball := hinside ρ hρ
  rw [hρeq] at hρball
  refine ⟨ρ, hρball, (hfix ρ).mp hρeq, ?_, ?_⟩
  · intro h
    have hbad := hd ρ hρ
    norm_num [h] at hbad
  · intro z hz hzero
    have h := hdist z ρ hz hρ
    rw [(hfix z).mpr hzero, hρeq] at h
    apply dist_eq_zero.mp
    linarith only [h, dist_nonneg (x := z) (y := ρ)]

def firstCenter : ℂ := ⟨1/4, 7067363/1000000⟩
abbrev firstRadius : ℝ := 1/4096
def firstDirection : ℂ := ⟨15069, -24342⟩

def openSpectralStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1/2}

theorem firstDisk_in_strip : closedBall firstCenter firstRadius ⊆ openSpectralStrip := by
  intro s hs
  have h := (Complex.abs_re_le_norm (s-firstCenter)).trans
    (by simpa only [mem_closedBall, dist_eq_norm] using hs)
  change |s.re-1/4| ≤ firstRadius at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  change 0 < s.re ∧ s.re < 1/2
  constructor <;> linarith [hl,hu]

theorem openSpectralStrip_open : IsOpen openSpectralStrip :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

private theorem cross_differentiable_on_strip : DifferentiableOn ℂ nativeCross openSpectralStrip := by
  have hA : Differentiable ℂ thirdFactor := by
    unfold thirdFactor
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
    fun_prop
  intro s hs
  have hp := Multiplicity.doubled_ne_pole hs.2
  have hZ := (Multiplicity.analytic_zeta hp).comp (Multiplicity.scale_analytic 2 s)
  have hnear : (fun z => correctionGap z * (thirdFactor z * riemannZeta (2*z))) =ᶠ[𝓝 s] nativeCross := by
    filter_upwards [openSpectralStrip_open.mem_nhds hs] with z hz
    rw [native_cross_eq z, sharedReference_eq (Multiplicity.doubled_ne_pole hz.2)]
    rfl
  exact (((correctionGap_entire s).mul ((hA s).mul hZ.differentiableAt)).congr_of_eventuallyEq
    hnear.symm).differentiableWithinAt

/-- Only the central enclosure and the derivative majorant enter this gap
test. Its conclusion bounds the correction gap on the entire disk. -/
theorem firstDisk_gap (hc : (11700 : ℝ) ≤ ‖correctionGap firstCenter‖)
    (hd : ∀ s ∈ closedBall firstCenter firstRadius, ‖deriv correctionGap s‖ ≤ 30000)
    {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    (11690 : ℝ) < ‖correctionGap s‖ := by
  have hcenter : firstCenter ∈ closedBall firstCenter firstRadius := mem_closedBall_self (by norm_num)
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => correctionGap_entire z) hd (convex_closedBall firstCenter firstRadius) hcenter hs
  have hr : ‖s-firstCenter‖ ≤ firstRadius := by simpa only [mem_closedBall, dist_eq_norm] using hs
  change ‖s-firstCenter‖ ≤ (1:ℝ)/4096 at hr
  have hh := norm_sub_norm_le (correctionGap firstCenter) (correctionGap s)
  rw [norm_sub_rev] at hh
  linarith only [hc, he, hh, mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 30000)]

structure FirstContourBounds : Prop where
  gapCenter : (11700 : ℝ) ≤ ‖correctionGap firstCenter‖
  gapDerivative : ∀ s ∈ closedBall firstCenter firstRadius, ‖deriv correctionGap s‖ ≤ 30000
  centerResidual : ‖nativeCross firstCenter / firstDirection‖ ≤ 1/10^6
  derivativeDefect : ∀ s ∈ closedBall firstCenter firstRadius,
    ‖1 - deriv nativeCross s / firstDirection‖ ≤ 1/4

/-- The count and the centered location are read on the cross-product. -/
theorem firstContour_read (hgap : ∀ s ∈ closedBall firstCenter firstRadius, correctionGap s ≠ 0)
    (hcenter : ‖nativeCross firstCenter / firstDirection‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ closedBall firstCenter firstRadius,
      ‖1 - deriv nativeCross s / firstDirection‖ ≤ 1/4) :
    ∃ ρ ∈ ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 → s = ρ) ∧
      weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
      firstCenter + weightedCircle firstCenter firstRadius nativeCross (fun s => s-firstCenter) = ρ := by
  have ha : firstDirection ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num [firstDirection] at hr
  have hf := cross_differentiable_on_strip
  have hpd : ∀ s ∈ closedBall firstCenter firstRadius, DifferentiableAt ℂ nativeCross s :=
    fun s hs => hf.differentiableAt (openSpectralStrip_open.mem_nhds (firstDisk_in_strip hs))
  have hc : ‖nativeCross firstCenter / firstDirection‖ < (3/4)*firstRadius :=
    lt_of_le_of_lt hcenter (by norm_num)
  obtain ⟨ρ,hρ,hzero,hder,hunique⟩ := unique_simple_zero_of_defect (by norm_num) ha hpd hc hdefect
  have hρD := ball_subset_closedBall hρ
  have hstrip := firstDisk_in_strip hρD
  have hsep : correction false ρ ≠ correction true ρ := by
    intro he
    exact hgap ρ hρD (sub_eq_zero.mpr he)
  have hζ := (native_cross_zero_iff hstrip.1 hstrip.2 hsep).mp hzero
  have hEval (p : ℂ → ℂ) (hp : Differentiable ℂ p) :
      weightedCircle firstCenter firstRadius nativeCross p = p ρ :=
    weightedCircle_of_simple_root openSpectralStrip_open firstDisk_in_strip hf hp hρ hzero hder hunique
  refine ⟨ρ, hρ, hzero, hder, hζ, hunique, hEval _ (differentiable_const _), ?_⟩
  have hp : Differentiable ℂ (fun s => s-firstCenter) := differentiable_id.sub_const _
  rw [hEval _ hp]
  ring

/-- The variation bound gives a quantitative gap as well as the contour
conclusions. All four input inequalities are listed in FirstContourBounds. -/
theorem firstContour_certificate (h : FirstContourBounds) :
    (∀ s ∈ closedBall firstCenter firstRadius, (11690 : ℝ) < ‖correctionGap s‖) ∧
    ∃ ρ ∈ ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 → s = ρ) ∧
      weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
      firstCenter + weightedCircle firstCenter firstRadius nativeCross (fun s => s-firstCenter) = ρ := by
  have gap (s : ℂ) (hs : s ∈ closedBall firstCenter firstRadius) :
      (11690 : ℝ) < ‖correctionGap s‖ := firstDisk_gap h.gapCenter h.gapDerivative hs
  refine ⟨gap, firstContour_read ?_ h.centerResidual h.derivativeDefect⟩
  intro s hs he
  have hbad := gap s hs
  norm_num [he] at hbad

#print axioms weightedCircle_of_simple_root
#print axioms unique_simple_zero_of_defect
#print axioms firstDisk_gap
#print axioms firstContour_read
#print axioms firstContour_certificate

end DottieOriented.NativeSpectrum
end
