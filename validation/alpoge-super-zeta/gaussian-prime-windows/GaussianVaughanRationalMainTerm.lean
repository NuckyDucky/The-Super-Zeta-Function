import GaussianDirichletVerticalGrowth
import GaussianVaughanRationalSplit
import GaussianVaughanConvolvedLeftLine
import GaussianVaughanPrimeInversion

/-! The abelian comparison with the original theta weight. Subtract
the Mellin transform of exp(-v)/v to remove the single pole at one. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex DirichletCharacter Filter MeasureTheory QuarticModel Set
open scoped Topology

noncomputable section

private abbrev M := archivedGaussianVaughanMultiplier
private abbrev χ₀ : DirichletCharacter ℂ archivedGaussianRationalLevel := 1
private abbrev χ₁ := archivedGaussianRationalChi4
private abbrev χ₂ := archivedGaussianNormCharacter
private abbrev χ₃ := χ₁ * χ₂

def archivedGaussianSplitKernel (v : ℝ) : ℂ :=
  dirichletKernelSum archivedGaussianSplitMangoldt (fun u => (archivedGaussianVaughanKernel u : ℂ)) v

private def reference (v : ℝ) : ℂ :=
  (v : ℂ) ^ (-1 : ℂ) • (Real.exp (-v) : ℂ)

private theorem reference_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin reference z (Gamma (z - 1)) := by
  have hpos : 0 < (z - 1).re := by rw [sub_re, one_re]; linarith
  have hc : MellinConvergent (fun v => (Real.exp (-v) : ℂ)) (z - 1) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using GammaIntegral_convergent hpos
  refine ⟨(MellinConvergent.cpow_smul (a := (-1 : ℂ))).mpr
    (by simpa only [← sub_eq_add_neg] using hc), ?_⟩
  change mellin (fun v : ℝ => (v : ℂ) ^ (-1 : ℂ) • (Real.exp (-v) : ℂ)) z = _
  rw [mellin_cpow_smul, ← sub_eq_add_neg, Gamma_eq_integral hpos, GammaIntegral_eq_mellin]

private def regularSum (z : ℂ) : ℂ :=
  -logDeriv (regularDirichlet χ₀) z + -logDeriv (regularDirichlet χ₁) z +
    -logDeriv (regularDirichlet χ₂) z + -logDeriv (regularDirichlet χ₃) z

private def principalNumerator (z : ℂ) : ℂ := M z - M 1 * Gamma z

private def residualMellin (z : ℂ) : ℂ :=
  M z * regularSum z + dslope principalNumerator 1 z

private theorem principalNumerator_one : principalNumerator 1 = 0 := by
  simp [principalNumerator, Gamma_one]

private theorem principalNumerator_analytic {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ principalNumerator z := by
  have hΓ : AnalyticAt ℂ Gamma z := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hOpen.mem_nhds (show z ∈ {w : ℂ | 0 < w.re} from hz)] with w hw
    apply differentiableAt_Gamma
    intro n hn
    change 0 < w.re at hw
    rw [hn, neg_re, natCast_re] at hw
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (archivedGaussianVaughanMultiplier_entire.analyticAt z).sub
    (analyticAt_const.mul hΓ)

private theorem principalRemainder_analytic {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (dslope principalNumerator 1) z := by
  by_cases h : z = 1
  · subst z
    exact Deduction.poleData_dslope (principalNumerator_analytic hz)
  have he : dslope principalNumerator 1 =ᶠ[𝓝 z] fun w => principalNumerator w / (w - 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1} : Set ℂ)ᶜ from h)] with w hw
    rw [dslope_of_ne _ hw, slope_def_field, principalNumerator_one, sub_zero, div_eq_inv_mul]
  exact ((principalNumerator_analytic hz).div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr h)).congr he.symm

private theorem residualMellin_analytic (hDir : DirichletLZerosOnLine)
    {z : ℂ} (hz : 1 / 2 < z.re) : AnalyticAt ℂ residualMellin z := by
  have hReg (χ : DirichletCharacter ℂ archivedGaussianRationalLevel) :
      AnalyticAt ℂ (fun w => -logDeriv (regularDirichlet χ) w) z := by
    have h := (regularDirichlet_differentiable χ).analyticAt z
    exact (h.deriv.div h (regularDirichlet_ne_zero hDir χ hz)).neg
  have hS : AnalyticAt ℂ regularSum z := (((hReg χ₀).add (hReg χ₁)).add
    (hReg χ₂)).add (hReg χ₃)
  exact ((archivedGaussianVaughanMultiplier_entire.analyticAt z).mul hS).add
    (principalRemainder_analytic (by linarith))

private theorem residual_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin (fun v => archivedGaussianSplitKernel v - M 1 * reference v) z (residualMellin z) := by
  have hR : HasMellin archivedGaussianSplitKernel z (M z * LSeries archivedGaussianSplitMangoldt z) :=
    dirichletKernelSum_hasMellin archivedGaussianSplitMangoldt
    (archivedGaussianVaughanKernel_hasMellin (zero_lt_one.trans hz))
    (archivedGaussianSplitMangoldt_summable hz)
  have hE := reference_hasMellin hz
  have he := hasMellin_const_smul hE.1 (M 1)
  have hf := hasMellin_sub hR.1 he.1
  refine ⟨hf.1, ?_⟩
  rw [show (fun v => archivedGaussianSplitKernel v - M 1 * reference v) =
    (fun v => archivedGaussianSplitKernel v - M 1 • reference v) from rfl, hf.2, he.2, hR.2, hE.2]
  simp only [smul_eq_mul]
  obtain ⟨h₁, h₂, h₃⟩ := archivedGaussianSplitCharacters_ne_one
  rw [archivedGaussianSplitMangoldt_LSeries hz]
  simp only [dirichlet_neg_logDeriv_eq_regular _ hz, if_neg h₁, if_neg h₂, if_neg h₃,
    if_true, add_zero]
  have hz₁ : z ≠ 1 := by rintro rfl; norm_num at hz
  have hΓ := Gamma_add_one (z - 1) (sub_ne_zero.mpr hz₁)
  rw [sub_add_cancel] at hΓ
  have hE' : Gamma (z - 1) = Gamma z / (z - 1) := by
    rw [hΓ, mul_comm, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hz₁)]
  rw [residualMellin, dslope_of_ne _ hz₁, slope_def_field, principalNumerator_one,
    sub_zero, principalNumerator, hE', div_eq_mul_inv]
  unfold regularSum
  ring

private theorem multiplier_weighted (k : ℕ) :
    ∃ C ≥ 0, ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
      (1 + |z.im|) ^ k * ‖M z‖ ≤ C := by
  obtain ⟨C, hC, hT⟩ := archivedGaussianThetaMellin_rapid_decay k
  refine ⟨2 * C, by positivity, fun z hl hr => ?_⟩
  have hD := gaussianScaleDifference_norm_on_right (a := 1 / 2) hl
  norm_num at hD
  change (1 + |z.im|) ^ k *
    ‖gaussianScaleDifference (1 / 2) z * (archivedMellin (z / 7) / 7)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (1 + |z.im|) ^ k * (2 * ‖archivedMellin (z / 7) / 7‖) := by gcongr
    _ = 2 * ((1 + |z.im|) ^ k * ‖archivedMellin (z / 7) / 7‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hT z (by linarith) (by linarith)) (by norm_num)

private theorem principalRemainder_weighted {a : ℝ} (ha : 1 / 2 < a) (ha₁ : a ≤ 1) :
    ∃ C ≥ 0, ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 / 2 →
      (1 + |z.im|) ^ (2 : ℕ) * ‖dslope principalNumerator 1 z‖ ≤ C := by
  obtain ⟨A, hA, hM⟩ := multiplier_weighted 2
  obtain ⟨B, hB, hΓ⟩ := gamma_rapid_decay_on_positive_strip (a := a) (b := 3 / 2)
    (by linarith) (by linarith) 2
  let Q := Complex.reProdIm (Icc a (3 / 2 : ℝ)) (Icc (-1) 1)
  have hQ : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hCont : ContinuousOn (fun z => ‖dslope principalNumerator 1 z‖) Q := by
    intro z hz
    have hh := principalRemainder_analytic (z := z) (by
      linarith [(Complex.mem_reProdIm.mp hz).1.1])
    exact hh.continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hQ.bddAbove_image hCont
  let C := A + ‖M 1‖ * B + 4 * max 0 D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun z hl hr => ?_⟩
  let T := 1 + |z.im|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  by_cases ht : |z.im| ≤ 1
  · have hmem : z ∈ Q := Complex.mem_reProdIm.mpr ⟨⟨hl, hr⟩, abs_le.mp ht⟩
    have hDz : ‖dslope principalNumerator 1 z‖ ≤ max 0 D :=
      (hD (mem_image_of_mem _ hmem)).trans (le_max_right _ _)
    have hT₂ : T ^ (2 : ℕ) ≤ 4 := by dsimp [T] at *; nlinarith [abs_nonneg z.im]
    exact (mul_le_mul hT₂ hDz (norm_nonneg _) (by positivity)).trans (by
      dsimp [C]
      linarith [mul_nonneg (norm_nonneg (M 1)) hB.le])
  have hIm : 1 ≤ ‖z - 1‖ := by
    have h := Complex.abs_im_le_norm (z - 1)
    rw [sub_im, one_im, sub_zero] at h
    exact (le_of_lt (lt_of_not_ge ht)).trans h
  have hz₁ : z ≠ 1 := by rintro rfl; norm_num at hIm
  have hD' : ‖dslope principalNumerator 1 z‖ ≤ ‖principalNumerator z‖ := by
    rw [dslope_of_ne _ hz₁, slope_def_field, principalNumerator_one, sub_zero, norm_div]
    exact div_le_self (norm_nonneg (principalNumerator z)) hIm
  calc
    _ ≤ T ^ (2 : ℕ) * ‖principalNumerator z‖ := mul_le_mul_of_nonneg_left hD' (by positivity)
    _ ≤ T ^ (2 : ℕ) * (‖M z‖ + ‖M 1‖ * ‖Gamma z‖) := by
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans_eq
        (by rw [norm_mul])) (by positivity)
    _ = T ^ (2 : ℕ) * ‖M z‖ + ‖M 1‖ * (T ^ (2 : ℕ) * ‖Gamma z‖) := by ring
    _ ≤ A + ‖M 1‖ * B := add_le_add (hM z (by linarith) hr)
      (mul_le_mul_of_nonneg_left (hΓ z hl hr) (norm_nonneg _))
    _ ≤ _ := by dsimp [C]; linarith [le_max_left (0 : ℝ) D]

private theorem residual_square_decay (hDir : DirichletLZerosOnLine) {a : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a ≤ 1) :
    ∃ C ≥ 0, ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 / 2 →
      ‖residualMellin z‖ ≤ C / (1 + |z.im|) ^ (2 : ℕ) := by
  obtain ⟨A, hA, hR⟩ := rationalDirichlet_logDeriv_critical_strip hDir
    archivedGaussianRationalLevel ha ha₁
  obtain ⟨B, hB, hM⟩ := multiplier_weighted 3
  obtain ⟨D, hD, hRem⟩ := principalRemainder_weighted ha ha₁
  refine ⟨4 * A * B + D, by positivity, fun z hl hr => ?_⟩
  let T := 1 + |z.im|
  have hT : 0 < T := by dsimp [T]; positivity
  have hLog : 1 + Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT]
  let C := A * T
  have hChar (χ : DirichletCharacter ℂ archivedGaussianRationalLevel) :
      ‖-logDeriv (regularDirichlet χ) z‖ ≤ C := by
    rw [norm_neg]
    exact (hR χ z hl (by linarith)).trans (mul_le_mul_of_nonneg_left hLog hA.le)
  have hSum : ‖regularSum z‖ ≤ 4 * C := by
    unfold regularSum
    calc
      _ ≤ ‖-logDeriv (regularDirichlet χ₀) z‖ + ‖-logDeriv (regularDirichlet χ₁) z‖ +
          ‖-logDeriv (regularDirichlet χ₂) z‖ + ‖-logDeriv (regularDirichlet χ₃) z‖ :=
        (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)) _)
      _ ≤ _ := by linarith [hChar χ₀, hChar χ₁, hChar χ₂, hChar χ₃]
  apply (le_div_iff₀ (pow_pos hT 2)).mpr
  calc
    _ ≤ (‖M z‖ * (4 * C) + ‖dslope principalNumerator 1 z‖) * T ^ (2 : ℕ) := by
      refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (by positivity)
      rw [norm_mul]
      exact add_le_add_left (mul_le_mul_of_nonneg_left hSum (norm_nonneg _)) _
    _ = 4 * A * (T ^ (3 : ℕ) * ‖M z‖) + T ^ (2 : ℕ) * ‖dslope principalNumerator 1 z‖ := by
      dsimp [C]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hM z (by linarith) hr) (by positivity))
      (hRem z hl hr)

private theorem residual_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt (fun u => archivedGaussianSplitKernel u - M 1 * reference u) v := by
  obtain ⟨C, hC, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hS : ContinuousAt archivedGaussianSplitKernel v := by
    apply dirichletKernelSum_continuousAt_of_power (s := 2) (by norm_num) hC hv
      (continuous_ofReal.comp_continuousOn archivedGaussianVaughanKernel_continuousOn) _
      (archivedGaussianSplitMangoldt_summable (by norm_num))
    intro u hu
    change ‖(archivedGaussianVaughanKernel u : ℂ)‖ ≤ _
    simpa only [norm_real, Real.norm_eq_abs] using hK u hu
  have hcp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) v :=
    (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hv)).comp continuous_ofReal.continuousAt
  exact hS.sub (continuousAt_const.mul (hcp.mul (continuous_ofReal.comp
    continuous_neg.rexp).continuousAt))

theorem archivedGaussianSplitKernel_main_term (hDir : DirichletLZerosOnLine) {a : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a ≤ 1) :
    ∃ C ≥ 0, ∀ v > (0 : ℝ),
      ‖archivedGaussianSplitKernel v - M 1 * reference v‖ ≤ C * v ^ (-a) := by
  let f := fun v => archivedGaussianSplitKernel v - M 1 * reference v
  let b : ℝ := 3 / 2
  obtain ⟨D, _, hD⟩ := residual_square_decay hDir ha ha₁
  have hab : a ≤ b := by dsimp [b]; linarith
  have hA (z : ℂ) (hl : a ≤ z.re) (_ : z.re ≤ b) : DifferentiableAt ℂ residualMellin z :=
    (residualMellin_analytic hDir (ha.trans_le hl)).differentiableAt
  have hI := verticalIntegrable_of_square_decay le_rfl hab hA hD
  have hR := verticalIntegrable_of_square_decay hab le_rfl hA hD
  let C := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖residualMellin (((a : ℝ) : ℂ) + (y : ℂ) * I)‖
  have hC : 0 ≤ C := mul_nonneg (by positivity [Real.pi_pos]) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨C, hC, fun v hv => ?_⟩
  have h₁ : MellinConvergent f (b : ℂ) :=
    (residual_hasMellin (by norm_num [b])).1
  have hEq (y : ℝ) : mellin f ((b : ℂ) + (y : ℂ) * I) =
      residualMellin ((b : ℂ) + (y : ℂ) * I) :=
    (residual_hasMellin (by norm_num [b, mul_re])).2
  have hInv : VerticalIntegrable (mellin f) b := hR.congr (Eventually.of_forall fun y => (hEq y).symm)
  change ‖f v‖ ≤ _
  rw [← mellinInv_mellin_eq _ _ hv h₁ hInv (residual_continuousAt hv),
    show mellinInv b (mellin f) v = mellinInv b residualMellin v by simp only [mellinInv, hEq],
    ← mellinInv_eq_of_square_decay hv hab hA hD]
  exact norm_mellinInv_le hv hI

theorem archivedGaussianSplitKernel_scaled (hDir : DirichletLZerosOnLine) {a : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a ≤ 1) :
    ∃ C ≥ 0, ∀ X ≥ (1 : ℝ),
      ‖archivedGaussianSplitKernel X⁻¹ - (X : ℂ) * M 1‖ ≤ C * X ^ a := by
  obtain ⟨A, hA, hMain⟩ := archivedGaussianSplitKernel_main_term hDir ha ha₁
  refine ⟨A + ‖M 1‖, by positivity, fun X hX => ?_⟩
  have hx := zero_lt_one.trans_le hX
  have hV := inv_pos.mpr hx
  have hError := hMain X⁻¹ hV
  rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv] at hError
  have hRef : reference X⁻¹ = ((X * Real.exp (-X⁻¹) : ℝ) : ℂ) := by
    rw [reference, smul_eq_mul, cpow_neg_one, ofReal_inv, inv_inv, ofReal_mul]
  have hDiff : |X * Real.exp (-X⁻¹) - X| ≤ 1 := by
    have h₀ : Real.exp (-X⁻¹) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h₁ : 1 - X⁻¹ ≤ Real.exp (-X⁻¹) := by linarith [Real.add_one_le_exp (-X⁻¹)]
    rw [abs_le]
    constructor
    · have h := mul_le_mul_of_nonneg_left h₁ hx.le
      rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at h
      linarith
    · linarith [mul_le_mul_of_nonneg_left h₀ hx.le]
  have hOne : 1 ≤ X ^ a := Real.one_le_rpow hX (by linarith)
  have hSmall : ‖M 1 * reference X⁻¹ - (X : ℂ) * M 1‖ ≤ ‖M 1‖ := by
    rw [hRef, mul_comm (X : ℂ) (M 1), ← mul_sub, norm_mul, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) hDiff
  calc
    _ ≤ ‖archivedGaussianSplitKernel X⁻¹ - M 1 * reference X⁻¹‖ +
        ‖M 1 * reference X⁻¹ - (X : ℂ) * M 1‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ A * X ^ a + ‖M 1‖ * X ^ a := add_le_add hError
      (hSmall.trans (le_mul_of_one_le_right (norm_nonneg _) hOne))
    _ = _ := by ring

#check archivedGaussianSplitKernel_scaled
#print axioms archivedGaussianSplitKernel_main_term
#print axioms archivedGaussianSplitKernel_scaled

end
end AlpogeSuperZeta
