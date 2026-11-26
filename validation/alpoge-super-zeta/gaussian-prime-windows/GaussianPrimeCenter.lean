import GaussianPrimeMesh
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! Recover the affine center of the actual signed Gaussian prime ramp from
the value and slope of the archived folded theta integral at one. -/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace QuarticModel

noncomputable section

private def thetaAtScale (t : ℝ) : ℝ :=
  archivedTheta (t / archivedThetaScale)

private theorem thetaAtScale_center_bound :
    (fun t => (thetaAtScale t : ℂ)) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound (2 * archivedThetaScale)
  have hc : 0 < 2 * archivedThetaScale := mul_pos (by norm_num) archivedThetaScale_pos
  have he : ∀ᶠ (t : ℝ) in 𝓝[>] 0, t < 1 / (2 * archivedThetaScale) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hc))
  filter_upwards [self_mem_nhdsWithin, he] with t ht ht'
  have ht₀ : 0 < t := ht
  let u := t⁻¹ / archivedThetaScale
  have hu : 2 ≤ u := by
    apply (le_div_iff₀ archivedThetaScale_pos).2
    rw [le_inv_comm₀ hc ht₀]
    simpa only [one_div] using ht'.le
  have hscale : t⁻¹ = archivedThetaScale * u := by
    dsimp [u]
    field_simp [archivedThetaScale_pos.ne']
  have hex : u * Real.exp (-u) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), one_mul]
    linarith [Real.add_one_le_exp u]
  simp only [thetaAtScale, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one,
    archivedTheta_reflection t ht₀, abs_mul, abs_of_pos (inv_pos.mpr ht₀)]
  calc
    _ ≤ t⁻¹ * (2 * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left (archivedTheta_exp_bound hu) (inv_nonneg.mpr ht₀.le)
    _ = (2 * archivedThetaScale) * (u * Real.exp (-u)) := by rw [hscale]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hex hc.le

private theorem thetaAtScale_locallyIntegrable :
    LocallyIntegrableOn (fun t => (thetaAtScale t : ℂ)) (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  apply Complex.continuous_ofReal.comp_continuousOn
  refine archivedTheta_continuous_positive.comp (continuous_id.div_const archivedThetaScale).continuousOn ?_
  exact fun t ht => div_pos (mem_Ioi.mp ht) archivedThetaScale_pos

private theorem thetaAtScale_integrable :
    IntegrableOn thetaAtScale (Ioi 0) := by
  have hb : (fun t => (thetaAtScale t : ℂ)) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    simpa only [neg_zero, Real.rpow_zero] using thetaAtScale_center_bound
  have h := mellinConvergent_of_isBigO_rpow_exp (one_div_pos.mpr archivedThetaScale_pos)
    thetaAtScale_locallyIntegrable archivedTheta_exponential_decay hb
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)
  have hi : IntegrableOn (fun t => (thetaAtScale t : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul] using h
  simpa [IntegrableOn] using hi.re

private theorem thetaAtScale_log_integral :
    IntegrableOn (fun t => thetaAtScale t * Real.log t) (Ioi 0) ∧
      deriv archivedMellin 1 = ↑(∫ t in Ioi (0 : ℝ), thetaAtScale t * Real.log t) := by
  have hb : (fun t => (thetaAtScale t : ℂ)) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    simpa only [neg_zero, Real.rpow_zero] using thetaAtScale_center_bound
  have ha : (fun t => (thetaAtScale t : ℂ)) =O[atTop] (· ^ (-(2 : ℝ))) :=
    archivedTheta_exponential_decay.trans
      (isLittleO_exp_neg_mul_rpow_atTop (one_div_pos.mpr archivedThetaScale_pos) (-(2 : ℝ))).isBigO
  obtain ⟨hc, hd⟩ := mellin_hasDerivAt_of_isBigO_rpow thetaAtScale_locallyIntegrable ha
    (show (1 : ℂ).re < 2 by norm_num) hb (show (0 : ℝ) < (1 : ℂ).re by norm_num)
  have hw (t : ℝ) : Real.log t • (thetaAtScale t : ℂ) =
      ((thetaAtScale t * Real.log t : ℝ) : ℂ) := by
    simp only [Complex.real_smul, Complex.ofReal_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · have hi : IntegrableOn (fun t => ((thetaAtScale t * Real.log t : ℝ) : ℂ)) (Ioi 0) := by
      simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul, hw] using hc
    simpa [IntegrableOn] using hi.re
  · change deriv (mellin (fun t => (thetaAtScale t : ℂ))) 1 = _
    have h := hd.deriv
    simpa only [mellin, sub_self, Complex.cpow_zero, one_smul, hw,
      integral_complex_ofReal] using h

private theorem invert_above_one :
    (fun t : ℝ => t⁻¹) '' Ioi 1 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu₁ : 1 < u := hu
    exact ⟨inv_pos.mpr (zero_lt_one.trans hu₁), inv_lt_one_of_one_lt₀ hu₁⟩
  · intro ht
    exact ⟨t⁻¹, (one_lt_inv₀ ht.1).mpr ht.2, inv_inv t⟩

private theorem fold_theta_moment (q : ℝ → ℝ)
    (hq : IntegrableOn (fun t => thetaAtScale t * q t) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), thetaAtScale t * q t) =
      ∫ t in Ioi (1 : ℝ), thetaAtScale t * (q t + t⁻¹ * q t⁻¹) := by
  let f (t : ℝ) := thetaAtScale t * q t
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hsub' : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ ht =>
    mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht))
  have he : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro h
      rcases le_or_gt t 1 with h₁ | h₁
      · exact Or.inl ⟨h, h₁⟩
      · exact Or.inr h₁
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    refine disjoint_left.mpr fun _ hx hy => ?_
    exact (not_lt_of_ge hx.2) hy
  have hadd := setIntegral_union hdisj measurableSet_Ioi (hq.mono_set hsub) (hq.mono_set hsub')
  rw [he] at hadd
  have hder (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) (Ioi 1) t :=
    (hasDerivAt_inv (zero_lt_one.trans ht).ne').hasDerivWithinAt
  have hflip := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder
    inv_injective.injOn f
  rw [invert_above_one, setIntegral_congr_set Ioo_ae_eq_Ioc] at hflip
  have hInt := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hder inv_injective.injOn f
  rw [invert_above_one] at hInt
  have hi := hInt.mp (hq.mono_set (fun _ ht => ht.1))
  change (∫ t in Ioi (0 : ℝ), f t) = _
  rw [hadd, hflip, ← integral_add hi (hq.mono_set hsub')]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have htheta : thetaAtScale t⁻¹ = t * thetaAtScale t := by
    simpa only [thetaAtScale, inv_inv] using archivedTheta_reflection t⁻¹ (inv_pos.mpr ht₀)
  simp only [f, smul_eq_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),
    htheta]
  field_simp [ht₀.ne']
  ring

/-- Value at one in the same folded normalization as the sampling code. -/
theorem archivedMellin_one_folded :
    archivedMellin 1 =
      ↑(∫ t in Ioi (1 : ℝ), thetaAtScale t * (1 + t⁻¹)) := by
  have h := fold_theta_moment (fun _ => 1) (by
    simpa only [mul_one] using thetaAtScale_integrable)
  simp only [mul_one] at h
  change (mellin (fun t => (thetaAtScale t : ℂ)) 1) = _
  simp only [mellin, sub_self, Complex.cpow_zero, one_smul, integral_complex_ofReal, h]

/-- Derivative at one in the folded normalization. -/
theorem archivedMellin_deriv_one_folded :
    deriv archivedMellin 1 =
      ↑(∫ t in Ioi (1 : ℝ), thetaAtScale t * ((1 - t⁻¹) * Real.log t)) := by
  obtain ⟨hi, hd⟩ := thetaAtScale_log_integral
  rw [hd, fold_theta_moment Real.log hi]
  simp only [Real.log_inv]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

private theorem logDeriv_scalePower :
    logDeriv (fun w : ℂ => (archivedThetaScale : ℂ) ^ w) 1 =
      (Real.log archivedThetaScale : ℂ) := by
  have hscale : (archivedThetaScale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have heq : (fun w : ℂ => (archivedThetaScale : ℂ) ^ w) =
      fun w : ℂ => Complex.exp ((Real.log archivedThetaScale : ℂ) * w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hscale, ← Complex.ofReal_log archivedThetaScale_pos.le]
  rw [heq, logDeriv_apply]
  have hd := (Complex.hasDerivAt_exp ((Real.log archivedThetaScale : ℂ) * 1)).comp
    1 ((hasDerivAt_id (1 : ℂ)).const_mul (Real.log archivedThetaScale : ℂ))
  change HasDerivAt (fun w : ℂ => Complex.exp ((Real.log archivedThetaScale : ℂ) * w))
    _ 1 at hd
  rw [hd.deriv, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _), mul_one]

/-- Removing the scale and Gamma completion gives the original Gaussian log derivative. -/
theorem archivedGaussian_logDeriv_one_folded :
    (logDeriv archivedGaussianFactor 1).re =
      (∫ t in Ioi (1 : ℝ), thetaAtScale t * ((1 - t⁻¹) * Real.log t)) /
        (∫ t in Ioi (1 : ℝ), thetaAtScale t * (1 + t⁻¹)) -
      Real.log archivedThetaScale + Real.eulerMascheroniConstant := by
  let c (w : ℂ) := (archivedThetaScale : ℂ) ^ w
  have hc : (archivedThetaScale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hcn : c 1 ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  have hcd : DifferentiableAt ℂ c 1 := differentiableAt_id.const_cpow (Or.inl hc)
  have hMn : archivedMellin 1 ≠ 0 := by
    intro hz
    exact AlpogeSuperZeta.quartic_gaussian_one_ne_zero (by simp [archivedGaussianFactor, hz])
  have hMd := archivedMellin_differentiable archivedTheta_reflection (1 : ℂ)
  have hgn : Complex.Gamma 1 ≠ 0 := by simp
  have hgd := Complex.hasDerivAt_Gamma_one.differentiableAt
  have heq : archivedGaussianFactor = fun w => archivedMellin w / (c w * Complex.Gamma w) := by
    funext w
    simp only [archivedGaussianFactor, c, div_eq_mul_inv, mul_inv_rev]
    ring
  have hd₀ : (fun w : ℂ => c w * Complex.Gamma w) 1 ≠ 0 := by
    change c 1 * Complex.Gamma 1 ≠ 0
    exact mul_ne_zero hcn hgn
  have hd₁ := logDeriv_div (f := archivedMellin) (g := fun w => c w * Complex.Gamma w)
    1 hMn hd₀ hMd (hcd.mul hgd)
  have hd₂ := logDeriv_mul (f := c) (g := Complex.Gamma) 1 hcn hgn hcd hgd
  have hlogC : logDeriv c 1 = (Real.log archivedThetaScale : ℂ) := logDeriv_scalePower
  rw [heq, hd₁, hd₂, hlogC,
    ← Complex.digamma_def, Complex.digamma_one, logDeriv_apply,
    archivedMellin_one_folded, archivedMellin_deriv_one_folded]
  rw [← Complex.ofReal_div]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

#print axioms archivedMellin_one_folded
#print axioms archivedMellin_deriv_one_folded
#print axioms archivedGaussian_logDeriv_one_folded

end
end QuarticModel

namespace AlpogeSuperZeta

open ArithmeticFunction QuarticModel

noncomputable section

/-- Independent finite evaluator and original ramp use this same affine coefficient. -/
def archivedGaussianPrimeLinearCenter : ℝ :=
  (logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient

theorem archivedGaussianPrimeLinearCenter_folded :
    archivedGaussianPrimeLinearCenter =
      (∫ t in Ioi (1 : ℝ), thetaAtScale t * ((1 - t⁻¹) * Real.log t)) /
        (∫ t in Ioi (1 : ℝ), thetaAtScale t * (1 + t⁻¹)) -
      Real.log archivedThetaScale + Real.eulerMascheroniConstant +
      gaussianHigherPrimeLinearCoefficient := by
  rw [archivedGaussianPrimeLinearCenter, archivedGaussian_logDeriv_one_folded]

theorem archivedGaussianPrimeOnlyRamp_eq_centered_finite (x : ℝ) :
    archivedGaussianPrimeOnlyRamp x =
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0) *
          max (x / n - 1) 0) + x * archivedGaussianPrimeLinearCenter := by
  simp only [archivedGaussianPrimeOnlyRamp, gaussianPrimeNormRamp, Deduction.ramp,
    Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re, archivedGaussianPrimeLinearCenter]
  ring

#print axioms archivedGaussianPrimeLinearCenter_folded
#print axioms archivedGaussianPrimeOnlyRamp_eq_centered_finite

end
end AlpogeSuperZeta
