import NativeDottieContour
import WeightedContourTransfer
import Mathlib.MeasureTheory.Function.Jacobian

/-!
Subtract the native correction and the known arithmetic factor on the
contour. At the origin the exact native cross-product count is three,
coming from a double correction zero and a simple arithmetic zero.
-/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Metric Set Filter MeasureTheory Asymptotics SuperZeta
open scoped Topology Real

abbrev belowPole : Set ℂ := {s : ℂ | s.re < 1/2}
private theorem belowPole_open : IsOpen belowPole := isOpen_lt continuous_re continuous_const

def doubledZeta (s : ℂ) : ℂ := riemannZeta (2*s)

private theorem doubledZeta_diff : DifferentiableOn ℂ doubledZeta belowPole :=
  fun s hs => ((Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole hs)).comp
    (Multiplicity.scale_analytic 2 s)).differentiableAt.differentiableWithinAt

private def powerThree (s : ℂ) : ℂ := (3:ℂ)^(2*s)
private def powerPi (s : ℂ) : ℂ := (π:ℂ)^(-(2*s))

private theorem powerThree_diff : Differentiable ℂ powerThree := by
  unfold powerThree
  simp only [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
  fun_prop

private theorem powerPi_diff : Differentiable ℂ powerPi := by
  unfold powerPi
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  fun_prop

private theorem thirdFactor_diff : Differentiable ℂ thirdFactor :=
  powerPi_diff.mul (powerThree_diff.sub (differentiable_const 1))

/-- The three channels need only be nonzero on the circumference. Their
interior zeros are accounted for with their multiplicities. -/
theorem native_contour_subtract_factors {c : ℂ} {r : ℝ} {p : ℂ → ℂ}
    (hr : 0 ≤ r) (hD : closedBall c r ⊆ belowPole) (hp : DifferentiableOn ℂ p belowPole)
    (hw : ∀ s ∈ sphere c r, correctionGap s ≠ 0) (ha : ∀ s ∈ sphere c r, thirdFactor s ≠ 0)
    (hz : ∀ s ∈ sphere c r, doubledZeta s ≠ 0) :
    weightedCircle c r nativeCross p - weightedCircle c r correctionGap p -
      weightedCircle c r thirdFactor p = weightedCircle c r doubledZeta p := by
  have he : Set.EqOn nativeCross (fun s => correctionGap s * (thirdFactor s * doubledZeta s)) belowPole := by
    intro s hs
    rw [native_cross_eq s, sharedReference_eq (Multiplicity.doubled_ne_pole hs)]
    rfl
  change WeightedContour.moment c r nativeCross p - WeightedContour.moment c r correctionGap p -
    WeightedContour.moment c r thirdFactor p = WeightedContour.moment c r doubledZeta p
  rw [WeightedContour.moment_congr hr belowPole_open hD he,
    WeightedContour.moment_mul hr belowPole_open hD correctionGap_entire.differentiableOn
      (thirdFactor_diff.differentiableOn.mul doubledZeta_diff) hp hw
      (fun s hs => mul_ne_zero (ha s hs) (hz s hs)),
    WeightedContour.moment_mul hr belowPole_open hD thirdFactor_diff.differentiableOn doubledZeta_diff hp ha hz]
  ring

theorem native_contour_subtract_gap {c : ℂ} {r : ℝ} {p : ℂ → ℂ}
    (hr : 0 ≤ r) (hD : closedBall c r ⊆ openSpectralStrip) (hp : Differentiable ℂ p)
    (hw : ∀ s ∈ sphere c r, correctionGap s ≠ 0) (hz : ∀ s ∈ sphere c r, doubledZeta s ≠ 0) :
    weightedCircle c r nativeCross p - weightedCircle c r correctionGap p =
      weightedCircle c r doubledZeta p := by
  have ha (s : ℂ) (hs : s ∈ closedBall c r) : thirdFactor s ≠ 0 :=
    thirdFactor_ne_zero (hD hs).1
  have h₁ : closedBall c r ⊆ belowPole := fun z hz' => (hD hz').2
  have hU : weightedCircle c r thirdFactor p = 0 :=
    WeightedContour.moment_unit hr belowPole_open h₁ thirdFactor_diff.differentiableOn
      hp.differentiableOn ha
  have h := native_contour_subtract_factors hr h₁ hp.differentiableOn hw
    (fun s hs => ha s (sphere_subset_closedBall hs)) hz
  rwa [hU, sub_zero] at h

private def nativeMellin (b : Bool) (s : ℂ) : ℂ := mellin (kernel b) (-(2*s))

private theorem kernel_top (b : Bool) :
    kernel b =O[atTop] (fun x : ℝ => Real.exp (-(1/2)*x)) := by
  refine isBigO_iff.mpr ⟨128/9, ?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [show -(1/2:ℝ)*x = -x/2 by ring] using kernel_tail_bound b hx

private theorem kernel_bottom (b : Bool) :
    kernel b =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-2:ℝ))) := by
  refine isBigO_iff.mpr ⟨16/3, ?_⟩
  have h : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [self_mem_nhdsWithin, h] with x hx h₁
  rw [neg_neg, show (2:ℝ) = (2:ℕ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  exact kernel_small_bound b (mem_Ioi.mp hx).le h₁.le

private theorem native_mellin_differentiable {s : ℂ} (b : Bool) (hs : s.re < 1) :
    DifferentiableAt ℂ (nativeMellin b) s := by
  have hm : DifferentiableAt ℂ (mellin (kernel b)) (-(2*s)) :=
    mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1/2)
      ((kernel_continuous b).continuousOn.locallyIntegrableOn measurableSet_Ioi)
      (kernel_top b) (kernel_bottom b) (by simp [two_mul]; linarith)
  exact hm.comp s (by fun_prop)

private theorem native_mellin_zero_converges (b : Bool) : MellinConvergent (kernel b) 0 :=
  mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1/2)
    ((kernel_continuous b).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (kernel_top b) (kernel_bottom b) (by norm_num)

private theorem mellin_at_zero_log (b : Bool) :
    Integrable (fun u : ℝ => kernel b (Real.exp u)) ∧
    nativeMellin b 0 = ∫ u, kernel b (Real.exp u) := by
  let F := fun x : ℝ => (x:ℂ)^((0:ℂ)-1) • kernel b x
  have hw (u : ℝ) : |Real.exp u| • F (Real.exp u) = kernel b (Real.exp u) := by
    dsimp [F]
    simp only [abs_of_pos (Real.exp_pos u), Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, zero_sub,
      Complex.cpow_neg, Complex.cpow_one,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'), one_mul]
  have hJ : Real.exp '' (univ : Set ℝ) = Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  have hd (u : ℝ) (_ : u ∈ (univ : Set ℝ)) : HasDerivWithinAt Real.exp (Real.exp u) univ u :=
    (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hi : IntegrableOn F (Real.exp '' (univ : Set ℝ)) := by
    rw [hJ]
    exact native_mellin_zero_converges b
  refine ⟨integrableOn_univ.mp
    (((integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd
      Real.exp_injective.injOn F).mp hi).congr_fun (fun u _ => hw u) MeasurableSet.univ), ?_⟩
  simp only [nativeMellin, mul_zero, neg_zero, mellin]
  change (∫ x in Ioi 0, F x) = _
  rw [← hJ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,
    setIntegral_univ]
  simp_rw [hw]

private def gapMellin (s : ℂ) : ℂ := nativeMellin false s - nativeMellin true s

private theorem gapMellin_zero_ne : gapMellin 0 ≠ 0 := by
  obtain ⟨hn, hn'⟩ := mellin_at_zero_log false
  obtain ⟨hp, hp'⟩ := mellin_at_zero_log true
  let F (u : ℝ) : ℂ := kernel true (Real.exp u) - kernel false (Real.exp u)
  have hF : Integrable F := hp.sub hn
  have hc : Continuous F := ((kernel_continuous true).comp Real.continuous_exp).sub
    ((kernel_continuous false).comp Real.continuous_exp)
  have hs (u : ℝ) : 0 < (F u).re := by
    obtain ⟨h₁,h₂⟩ := kernel_signs (Real.exp_pos u)
    simp only [F, sub_re, kernel, ofReal_re]
    linarith
  have hpos : 0 < ∫ u, (F u).re :=
    integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp hc) hF.re
      (fun u => (hs u).le) (hs 0).ne'
  intro he
  have he' : (∫ u, kernel false (Real.exp u)) - (∫ u, kernel true (Real.exp u)) = 0 := by
    simpa only [gapMellin, hn', hp'] using he
  have hRe : (∫ u, (F u).re) = (∫ u, F u).re := integral_re hF
  rw [hRe] at hpos
  have hz : (∫ u, F u) = 0 := by
    dsimp only [F]
    rw [integral_sub hp hn, ← neg_sub, he', neg_zero]
  norm_num [hz] at hpos

private def firstSine (s : ℂ) : ℂ := Complex.sin ((π:ℂ)*s)
private theorem firstSine_diff : Differentiable ℂ firstSine := by unfold firstSine; fun_prop
private theorem firstSine_deriv_zero : deriv firstSine 0 = (π:ℂ) := by
  have h := (((hasDerivAt_id (0:ℂ)).const_mul (π:ℂ)).csin).deriv
  simpa [firstSine] using h

private def gapUnit (s : ℂ) : ℂ :=
  (2/(π:ℂ)) * dslope firstSine 0 s * gapMellin s

private theorem gapUnit_diff : DifferentiableOn ℂ gapUnit belowPole := by
  have hs : Differentiable ℂ (dslope firstSine 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr firstSine_diff.differentiableOn)
  have hm : DifferentiableOn ℂ gapMellin belowPole := by
    intro s hs'
    have hc : s.re < 1/2 := hs'
    have h₁ : s.re < 1 := by linarith
    exact ((native_mellin_differentiable false h₁).sub
      (native_mellin_differentiable true h₁)).differentiableWithinAt
  exact (((differentiable_const _).mul hs).differentiableOn).mul hm

private theorem gapUnit_zero_ne : gapUnit 0 ≠ 0 := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [gapUnit, dslope_same, firstSine_deriv_zero, div_mul_cancel₀ _ hπ]
  exact mul_ne_zero (by norm_num) gapMellin_zero_ne

private theorem gap_factors_at_origin {s : ℂ} (hs : s.re < 1) :
    correctionGap s = s^2 * gapUnit s := by
  have h : s * dslope firstSine 0 s = Complex.sin ((π:ℂ)*s) := by
    simpa [firstSine, smul_eq_mul] using sub_smul_dslope firstSine (0:ℂ) s
  rw [correctionGap, correction_integral false hs, correction_integral true hs, gapUnit, gapMellin,
    nativeMellin, nativeMellin, ← h]
  ring

private def arithmeticUnit (s : ℂ) : ℂ := powerPi s * dslope powerThree 0 s

private theorem arithmeticUnit_diff : Differentiable ℂ arithmeticUnit :=
  powerPi_diff.mul (differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr
    powerThree_diff.differentiableOn))

private theorem arithmetic_factors_at_origin (s : ℂ) :
    thirdFactor s = s * arithmeticUnit s := by
  have h : s * dslope powerThree 0 s = powerThree s-1 := by
    simpa [powerThree, smul_eq_mul] using sub_smul_dslope powerThree (0:ℂ) s
  change powerPi s * (powerThree s-1) = s*(powerPi s * dslope powerThree 0 s)
  rw [← h]
  ring

private theorem arithmeticUnit_zero_ne : arithmeticUnit 0 ≠ 0 := by
  have he : powerThree = fun s => Complex.exp ((2*Complex.log 3)*s) := by
    funext s
    rw [powerThree, Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
    congr 1
    ring
  have hd : deriv powerThree 0 = 2*Complex.log 3 := by
    rw [he]
    simpa using (((hasDerivAt_id (0:ℂ)).const_mul (2*Complex.log 3)).cexp).deriv
  have hn : Complex.log (3:ℂ) ≠ 0 := by
    rw [show (3:ℂ) = (((3:ℝ)):ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 3)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [arithmeticUnit, dslope_same, powerPi, mul_zero, neg_zero, Complex.cpow_zero, one_mul, hd]
  exact mul_ne_zero (by norm_num) hn

/-- There are arbitrarily small origin circles for which the marked count
is three while the ordinary count is zero. This exact control needs no
external numerical enclosure. -/
theorem origin_contour_counts :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → ∀ p : ℂ → ℂ, Differentiable ℂ p →
      weightedCircle 0 r nativeCross p = 3*p 0 ∧
      weightedCircle 0 r correctionGap p = 2*p 0 ∧
      weightedCircle 0 r thirdFactor p = p 0 ∧
      weightedCircle 0 r doubledZeta p = 0 := by
  have h₀ : (0:ℂ) ∈ belowPole := by norm_num [belowPole]
  have ho := belowPole_open.mem_nhds h₀
  have hz₀ : doubledZeta 0 ≠ 0 := by norm_num [doubledZeta, riemannZeta_zero]
  have hU := ((gapUnit_diff.differentiableAt ho).continuousAt.eventually_ne gapUnit_zero_ne)
  have hV := ((arithmeticUnit_diff 0).continuousAt.eventually_ne arithmeticUnit_zero_ne)
  have hZ := ((doubledZeta_diff.differentiableAt ho).continuousAt.eventually_ne hz₀)
  have hev : ∀ᶠ s : ℂ in 𝓝 0,
      s ∈ belowPole ∧ gapUnit s ≠ 0 ∧ arithmeticUnit s ≠ 0 ∧ doubledZeta s ≠ 0 := by
    filter_upwards [ho,hU,hV,hZ] with s h₁ h₂ h₃ h₄
    exact ⟨h₁,h₂,h₃,h₄⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd p hp
  have nonzeros (s : ℂ) (hs : s ∈ closedBall (0:ℂ) r) :
      s ∈ belowPole ∧ gapUnit s ≠ 0 ∧ arithmeticUnit s ≠ 0 ∧ doubledZeta s ≠ 0 :=
    hball (mem_ball.mpr ((mem_closedBall.mp hs).trans_lt hrd))
  have hD : closedBall (0:ℂ) r ⊆ belowPole := fun s hs => (nonzeros s hs).1
  have hG : Set.EqOn correctionGap (fun s => (s-(0:ℂ))^2 * gapUnit s) belowPole := by
    intro s hs
    have h := (show s.re < 1/2 from hs)
    simpa only [sub_zero] using gap_factors_at_origin (show s.re < 1 by linarith)
  have hA : Set.EqOn thirdFactor (fun s => (s-(0:ℂ))^1 * arithmeticUnit s) belowPole := by
    intro s _
    simpa only [sub_zero, pow_one] using arithmetic_factors_at_origin s
  have hC : Set.EqOn nativeCross
      (fun s => (s-(0:ℂ))^3*(gapUnit s*arithmeticUnit s*doubledZeta s)) belowPole := by
    intro s hs
    rw [native_cross_eq, sharedReference_eq (Multiplicity.doubled_ne_pole hs)]
    change correctionGap s * (thirdFactor s * doubledZeta s) = _
    rw [hG hs, hA hs]
    ring
  have ha := mem_ball_self (x := (0:ℂ)) hr
  have hCm := WeightedContour.moment_local_power ha 3 hp belowPole_open hD
    ((gapUnit_diff.mul arithmeticUnit_diff.differentiableOn).mul doubledZeta_diff)
    (fun s hs => mul_ne_zero (mul_ne_zero (nonzeros s hs).2.1 (nonzeros s hs).2.2.1)
      (nonzeros s hs).2.2.2) hC
  have hGm := WeightedContour.moment_local_power ha 2 hp belowPole_open hD gapUnit_diff
    (fun s hs => (nonzeros s hs).2.1) hG
  have hAm := WeightedContour.moment_local_power ha 1 hp belowPole_open hD
    arithmeticUnit_diff.differentiableOn (fun s hs => (nonzeros s hs).2.2.1) hA
  refine ⟨?_,?_,?_,WeightedContour.moment_unit hr.le belowPole_open hD doubledZeta_diff
    hp.differentiableOn (fun s hs => (nonzeros s hs).2.2.2)⟩
  · exact_mod_cast hCm
  · exact_mod_cast hGm
  · simpa using hAm

#print axioms native_contour_subtract_factors
#print axioms native_contour_subtract_gap
#print axioms origin_contour_counts

end DottieOriented.NativeSpectrum
end
