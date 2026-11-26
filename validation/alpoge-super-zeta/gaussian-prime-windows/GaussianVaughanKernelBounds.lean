import GaussianVaughanWindowCriterion

/-! Power envelopes for the actual two-scale theta, including the endpoint
integral that is removed when the cutoff starts at one. -/

namespace AlpogeSuperZeta

open Asymptotics Complex Filter MeasureTheory Set QuarticModel
open scoped Topology

noncomputable section

private def thetaAtNormScale (t : ℝ) : ℝ := archivedTheta (t / archivedThetaScale)

private theorem thetaAtNormScale_continuousOn : ContinuousOn thetaAtNormScale (Ioi 0) := by
  exact archivedTheta_continuous_positive.comp (continuous_id.div_const _).continuousOn
    (fun t ht => div_pos ht archivedThetaScale_pos)

private theorem thetaAtNormScale_small {t : ℝ} (ht : 0 < t)
    (hs : t ≤ (2 * archivedThetaScale)⁻¹) :
    |thetaAtNormScale t| ≤ 2 * archivedThetaScale := by
  have hc := archivedThetaScale_pos
  have h2c : 0 < 2 * archivedThetaScale := by positivity
  let u := t⁻¹ / archivedThetaScale
  have hu : 2 ≤ u := (le_div_iff₀ hc).2 ((le_inv_comm₀ h2c ht).2 hs)
  have htu : t⁻¹ = archivedThetaScale * u := by
    dsimp [u]
    field_simp [hc.ne']
  have hExp : u * Real.exp (-u) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), one_mul]
    linarith [Real.add_one_le_exp u]
  rw [thetaAtNormScale, archivedTheta_reflection t ht, abs_mul, abs_of_pos (inv_pos.mpr ht)]
  calc
    t⁻¹ * |archivedTheta u| ≤ t⁻¹ * (2 * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left (archivedTheta_exp_bound hu) (inv_nonneg.mpr ht.le)
    _ = (2 * archivedThetaScale) * (u * Real.exp (-u)) := by rw [htu]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp h2c.le

private theorem thetaAtNormScale_global_power {a : ℝ} (ha : 0 ≤ a) :
    ∃ D ≥ (0 : ℝ), ∀ t > (0 : ℝ), |thetaAtNormScale t| ≤ D * t ^ (-a) := by
  have hTop := archivedTheta_exponential_decay.trans
    (isLittleO_exp_neg_mul_rpow_atTop (one_div_pos.mpr archivedThetaScale_pos) (-a)).isBigO
  obtain ⟨D₁, hD₁, hTop⟩ := hTop.exists_pos
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp hTop.bound
  let t₀ := min 1 (2 * archivedThetaScale)⁻¹
  have ht₀ : 0 < t₀ := lt_min one_pos (inv_pos.mpr (mul_pos two_pos archivedThetaScale_pos))
  let B := max t₀ t₁
  have hcont : ContinuousOn (fun t : ℝ => |thetaAtNormScale t| * t ^ a) (Ioi 0) :=
    thetaAtNormScale_continuousOn.abs.mul
      (continuousOn_of_forall_continuousAt fun t ht =>
        Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))
  obtain ⟨D₂, hD₂⟩ := isCompact_Icc.bddAbove_image
    (hcont.mono (show Icc t₀ B ⊆ Ioi 0 from fun t h => ht₀.trans_le h.1))
  let D := max (max D₁ D₂) (2 * archivedThetaScale)
  have hD₁' : D₁ ≤ D := (le_max_left _ _).trans (le_max_left _ _)
  have hD₂' : D₂ ≤ D := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨D, hD₁.le.trans hD₁', fun t ht => ?_⟩
  by_cases htSmall : t ≤ t₀
  · have hθ := thetaAtNormScale_small ht (htSmall.trans (min_le_right _ _))
    have hpow : 1 ≤ t ^ (-a) := by
      rw [← Real.rpow_zero t]
      exact Real.rpow_le_rpow_of_exponent_ge ht (htSmall.trans (min_le_left _ _)) (neg_nonpos.mpr ha)
    calc
      |thetaAtNormScale t| ≤ 2 * archivedThetaScale := hθ
      _ ≤ D := le_max_right _ _
      _ ≤ D * t ^ (-a) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (hD₁.le.trans hD₁')
  by_cases htBig : B ≤ t
  · have hb := ht₁ t ((le_max_right _ _).trans htBig)
    have hb' : |thetaAtNormScale t| ≤ D₁ * t ^ (-a) := by
      simpa only [thetaAtNormScale, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht.le _)] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right hD₁' (Real.rpow_nonneg ht.le _))
  have htMid : t ∈ Icc t₀ B := ⟨(not_le.mp htSmall).le, (not_le.mp htBig).le⟩
  have hmid : |thetaAtNormScale t| * t ^ a ≤ D :=
    (hD₂ (mem_image_of_mem _ htMid)).trans hD₂'
  rw [Real.rpow_neg ht.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ht a)).2 hmid

theorem archivedGaussianVaughanKernel_continuousOn :
    ContinuousOn archivedGaussianVaughanKernel (Ioi 0) := by
  have hH : ContinuousOn archivedGaussianSeventhFreeKernel (Ioi 0) :=
    thetaAtNormScale_continuousOn.comp (continuous_pow 7).continuousOn
      (fun v hv => show 0 < v ^ 7 from pow_pos (show 0 < v from hv) _)
  exact hH.sub ((hH.comp (continuous_const.mul continuous_id).continuousOn
    (fun v hv => show 0 < 2 * v from mul_pos two_pos (show 0 < v from hv))).const_mul _)

theorem archivedGaussianVaughanKernel_powerBound {a : ℝ} (ha : 0 ≤ a) :
    ∃ D ≥ (0 : ℝ), ∀ v > (0 : ℝ), |archivedGaussianVaughanKernel v| ≤ D * v ^ (-a) := by
  obtain ⟨D, hD, hθ⟩ := thetaAtNormScale_global_power (div_nonneg ha (by norm_num : (0 : ℝ) ≤ 7))
  have hH (v : ℝ) (hv : 0 < v) :
      |archivedGaussianSeventhFreeKernel v| ≤ D * v ^ (-a) := by
    have hh := hθ (v ^ 7) (pow_pos hv _)
    have he : (v ^ (7 : ℕ)) ^ (-(a / 7)) = v ^ (-a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le,
        show (↑(7 : ℕ) : ℝ) * -(a / 7) = -a by push_cast; ring]
    rw [he] at hh
    exact hh
  let c := Real.exp (1 / 2 * Real.log 2)
  refine ⟨D + c * D * (2 : ℝ) ^ (-a), by dsimp [c]; positivity, fun v hv => ?_⟩
  have h2v : 0 < 2 * v := mul_pos (by norm_num) hv
  change |archivedGaussianSeventhFreeKernel v - c * archivedGaussianSeventhFreeKernel (2 * v)| ≤ _
  calc
    _ ≤ |archivedGaussianSeventhFreeKernel v| + c * |archivedGaussianSeventhFreeKernel (2 * v)| := by
      simpa only [abs_mul, abs_of_pos (show 0 < c from Real.exp_pos _)] using
        abs_sub (archivedGaussianSeventhFreeKernel v) (c * archivedGaussianSeventhFreeKernel (2 * v))
    _ ≤ D * v ^ (-a) + c * (D * (2 * v) ^ (-a)) :=
      add_le_add (hH v hv) (mul_le_mul_of_nonneg_left (hH (2 * v) h2v) (Real.exp_pos _).le)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.le]; ring

/-- The signed sum has a global bound by every power greater than one.
For powers larger than two this also bounds its small-scale endpoint. -/
theorem archivedGaussianVaughanSum_powerBound {a : ℝ} (ha : 1 < a) :
    ∃ C ≥ (0 : ℝ), ∀ x > (0 : ℝ), |archivedGaussianVaughanSum x| ≤ C * x ^ a := by
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (zero_lt_one.trans ha).le
  let b (n : ℕ) := ‖LSeries.term archivedGaussianMangoldt (a : ℂ) n‖
  have hb : Summable b := (archivedGaussianMangoldt_summable (by simpa using ha)).norm
  refine ⟨D * ∑' n, b n, mul_nonneg hD (tsum_nonneg fun _ => norm_nonneg _), fun x hx => ?_⟩
  let F (n : ℕ) := (archivedGaussianMangoldt n).re * archivedGaussianVaughanKernel (n / x)
  have hf (n : ℕ) : ‖F n‖ ≤ (D * x ^ a) * b n := by
    by_cases hn : n = 0
    · subst n
      simp [F, b]
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hdiv := div_pos hn₀ hx
    have hfactor : ((n : ℝ) / x) ^ (-a) = x ^ a / (n : ℝ) ^ a := by
      rw [Real.div_rpow hn₀.le hx.le, Real.rpow_neg hn₀.le, Real.rpow_neg hx.le, inv_div_inv]
    dsimp only [F, b]
    rw [Real.norm_eq_abs, abs_mul, LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hn₀, ofReal_re]
    calc
      _ ≤ ‖archivedGaussianMangoldt n‖ * (D * ((n : ℝ) / x) ^ (-a)) :=
        mul_le_mul (abs_re_le_norm _) (hK _ hdiv) (abs_nonneg _)
          (norm_nonneg _)
      _ = _ := by rw [hfactor]; ring
  have hfs : Summable (fun n => ‖F n‖) := (hb.mul_left (D * x ^ a)).of_nonneg_of_le
    (fun _ => norm_nonneg _) hf
  rw [archivedGaussianVaughanSum, if_pos hx, ← Real.norm_eq_abs]
  change ‖∑' n, F n‖ ≤ _
  refine (norm_tsum_le_tsum_norm hfs).trans ?_
  calc
    _ ≤ ∑' n, (D * x ^ a) * b n := hfs.tsum_le_tsum hf (hb.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

theorem archivedGaussianVaughanSum_growth :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianVaughanSum x| ≤ C * x ^ (2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := archivedGaussianVaughanSum_powerBound (by norm_num : (1 : ℝ) < 2)
  exact ⟨C, hC, fun x hx => h x (zero_lt_one.trans_le hx)⟩

/-- The filtered theta's Mellin transform is exactly the multiplier at
the Gaussian spectral coordinate. -/
theorem archivedGaussianVaughanKernel_hasMellin {z : ℂ} (hz : 0 < z.re) :
    HasMellin (fun v => ↑(archivedGaussianVaughanKernel v)) z
      (archivedGaussianVaughanMultiplier z) := by
  let f : ℝ → ℂ := fun t => thetaAtNormScale t
  have hLoc : LocallyIntegrableOn f (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn thetaAtNormScale_continuousOn).locallyIntegrableOn
      measurableSet_Ioi
  have hBot : f =O[𝓝[>] (0 : ℝ)] (fun t => t ^ (-(0 : ℝ))) := by
    obtain ⟨C, _, hC⟩ := thetaAtNormScale_global_power (a := 0) le_rfl
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
    simpa only [f, Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, abs_one,
      mul_one] using hC t ht
  have hConv : MellinConvergent f (z / 7) :=
    mellinConvergent_of_isBigO_rpow_exp (one_div_pos.mpr archivedThetaScale_pos)
      hLoc archivedTheta_exponential_decay hBot (by rw [div_ofNat_re]; positivity)
  let H : ℝ → ℂ := fun v => archivedGaussianSeventhFreeKernel v
  have hH : H = fun v => f (v ^ (7 : ℝ)) := by
    funext v
    simp only [H, f, thetaAtNormScale, archivedGaussianSeventhFreeKernel,
      ← Real.rpow_natCast]
    norm_num
  have hConvH : MellinConvergent H z := by
    rw [hH]
    exact (MellinConvergent.comp_rpow (a := (7 : ℝ)) (by norm_num)).mpr
      (by norm_cast)
  have hHval : mellin H z = archivedMellin (z / 7) / 7 := by
    rw [hH, mellin_comp_rpow, Complex.real_smul]
    norm_num [div_eq_mul_inv, mul_comm, archivedMellin, f, thetaAtNormScale]
  have h := gaussianHalfScale_mellin H hConvH
  rw [hHval] at h
  simpa only [archivedGaussianVaughanKernel, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_exp, H, archivedGaussianVaughanMultiplier] using h

private def archivedGaussianVaughanEndpointWeight : ℝ → ℂ :=
  (Iic 1).indicator fun x => (archivedGaussianVaughanSum x : ℂ)

def archivedGaussianVaughanEndpoint (z : ℂ) : ℂ :=
  mellin archivedGaussianVaughanEndpointWeight (-z)

theorem archivedGaussianVaughanEndpoint_entire :
    Differentiable ℂ archivedGaussianVaughanEndpoint := by
  have hmeas : Measurable archivedGaussianVaughanEndpointWeight :=
    (Complex.continuous_ofReal.measurable.comp
    archivedGaussianVaughanSum_measurable).indicator (s := Iic (1 : ℝ)) measurableSet_Iic
  have hLoc : LocallyIntegrableOn archivedGaussianVaughanEndpointWeight (Ioi 0) := by
    obtain ⟨C, hC, hF⟩ := archivedGaussianVaughanSum_powerBound (by norm_num : (1 : ℝ) < 2)
    apply IntegrableOn.locallyIntegrableOn
    have hI : IntegrableOn archivedGaussianVaughanEndpointWeight (Ioc 0 1) := by
      apply IntegrableOn.of_bound (measure_Ioc_lt_top) hmeas.aemeasurable.aestronglyMeasurable C
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
      rw [archivedGaussianVaughanEndpointWeight, indicator_of_mem (mem_Iic.mpr hx.2),
        Complex.norm_real, Real.norm_eq_abs]
      exact (hF x hx.1).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hx.1.le hx.2 (by norm_num : (0 : ℝ) ≤ 2)) hC)
    have hZero : IntegrableOn archivedGaussianVaughanEndpointWeight (Ioi 1) := by
      refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Ioi 1) volume).congr_fun
        (g := archivedGaussianVaughanEndpointWeight) ?_ measurableSet_Ioi
      intro t ht
      change 1 < t at ht
      rw [archivedGaussianVaughanEndpointWeight,
        indicator_of_notMem (show t ∉ Iic (1 : ℝ) from not_le.mpr ht)]
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hI.union hZero
  intro z
  let a := |z.re| + 2
  have ha : 1 < a := by dsimp [a]; linarith [abs_nonneg z.re]
  have hbot : archivedGaussianVaughanEndpointWeight =O[𝓝[>] (0 : ℝ)] (fun x => x ^ (-(-a))) := by
    obtain ⟨C, _, hF⟩ := archivedGaussianVaughanSum_powerBound ha
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with x hx hx'
    change 0 < x at hx
    rw [archivedGaussianVaughanEndpointWeight, indicator_of_mem (mem_Iic.mpr hx'.le),
      Complex.norm_real, Real.norm_eq_abs, neg_neg,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    exact hF x hx
  have hTop : archivedGaussianVaughanEndpointWeight =O[atTop] (fun x => x ^ (-a)) := by
    apply IsBigO.of_bound 0
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp [archivedGaussianVaughanEndpointWeight, not_le.mpr hx]
  have hσ : (-z).re < a := by simp only [neg_re, a]; linarith [neg_abs_le z.re]
  have hσ' : -a < (-z).re := by simp only [neg_re, a]; linarith [le_abs_self z.re]
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hσ hbot hσ').comp z
    (differentiableAt_id.neg)

theorem archivedGaussianVaughanEndpoint_eq_integral (z : ℂ) :
    archivedGaussianVaughanEndpoint z =
      ∫ x in Ioc (0 : ℝ) 1, (archivedGaussianVaughanSum x : ℂ) * (x : ℂ) ^ (-z - 1) := by
  let f (x : ℝ) := (archivedGaussianVaughanSum x : ℂ) * (x : ℂ) ^ (-z - 1)
  have hEq : EqOn (fun x : ℝ => (x : ℂ) ^ (-z - 1) • archivedGaussianVaughanEndpointWeight x)
      ((Iic 1).indicator f) (Ioi 0) := by
    intro x _
    change (x : ℂ) ^ (-z - 1) • archivedGaussianVaughanEndpointWeight x = _
    rw [archivedGaussianVaughanEndpointWeight, smul_eq_mul, mul_comm]
    exact (indicator_mul_left (Iic 1) (fun t => (archivedGaussianVaughanSum t : ℂ))
      (fun t => (t : ℂ) ^ (-z - 1))).symm
  unfold archivedGaussianVaughanEndpoint mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hEq]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

#print axioms archivedGaussianVaughanKernel_continuousOn
#print axioms archivedGaussianVaughanKernel_powerBound
#print axioms archivedGaussianVaughanSum_powerBound
#print axioms archivedGaussianVaughanSum_growth
#print axioms archivedGaussianVaughanKernel_hasMellin
#print axioms archivedGaussianVaughanEndpoint_entire
#print axioms archivedGaussianVaughanEndpoint_eq_integral

end
end AlpogeSuperZeta
