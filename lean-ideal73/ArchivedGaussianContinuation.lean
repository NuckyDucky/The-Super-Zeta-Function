import ArchivedThetaBounds

/-! The analytic consequences of the archived Poisson reflection. Keeping
the reflection as a named premise here lets the Fourier proof be replayed
independently of the Mellin and ideal-count proofs. -/

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace QuarticModel

open FieldCoefficientTransfer ArtinPrimitiveRootsConjecture

def ArchivedThetaReflects : Prop :=
  ∀ t : ℝ, 0 < t → archivedTheta (t/archivedThetaScale) = t⁻¹*archivedTheta (t⁻¹/archivedThetaScale)

theorem archivedMellin_reflects (href : ArchivedThetaReflects) (w : ℂ) :
    archivedMellin (1-w) = archivedMellin w := by
  let f (t : ℝ) : ℂ := archivedTheta (t/archivedThetaScale)
  change mellin f (1-w) = mellin f w
  calc
    _ = mellin (fun t => f t⁻¹) (w-1) := by rw [mellin_comp_inv, neg_sub]
    _ = mellin (fun t => (t : ℂ)^(1 : ℂ) • f t) (w-1) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have h := href t⁻¹ (inv_pos.mpr ht0)
      rw [inv_inv] at h
      have hf : f t⁻¹ = (t : ℂ)^(1 : ℂ) • f t := by
        simpa only [f, Complex.cpow_one, smul_eq_mul, Complex.ofReal_mul] using
          congrArg (fun u : ℝ => (u : ℂ)) h
      exact congrArg (fun u : ℂ => (t : ℂ)^(w-1-1) • u) hf
    _ = _ := by rw [mellin_cpow_smul, sub_add_cancel]

private theorem archivedTheta_center_bound (href : ArchivedThetaReflects) :
    (fun t : ℝ => (archivedTheta (t/archivedThetaScale) : ℂ)) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound (2*archivedThetaScale)
  have hs : 0 < 2*archivedThetaScale := mul_pos (by norm_num) archivedThetaScale_pos
  have hlt : ∀ᶠ (t : ℝ) in 𝓝[>] 0, t < 1/(2*archivedThetaScale) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hs))
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht'
  have ht0 : 0 < t := ht
  have hu : 2 ≤ t⁻¹/archivedThetaScale := by
    apply (le_div_iff₀ archivedThetaScale_pos).2
    rw [le_inv_comm₀ hs ht0]
    simpa only [one_div] using ht'.le
  let u := t⁻¹/archivedThetaScale
  have hb := archivedTheta_exp_bound hu
  have hex : u * Real.exp (-u) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), one_mul]
    linarith [Real.add_one_le_exp u]
  have hscale : t⁻¹ = archivedThetaScale*u := by
    dsimp [u]
    field_simp [archivedThetaScale_pos.ne']
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, href t ht0, abs_mul, abs_of_pos (inv_pos.mpr ht0)]
  calc
    _ ≤ t⁻¹ * (2*Real.exp (-u)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)
    _ = (2*archivedThetaScale)*(u*Real.exp (-u)) := by rw [hscale]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hex hs.le

private theorem archivedMellin_differentiable_right (href : ArchivedThetaReflects)
    {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ archivedMellin w := by
  have hcont : ContinuousOn (fun t : ℝ => (archivedTheta (t/archivedThetaScale) : ℂ)) (Ioi 0) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    refine archivedTheta_continuous_positive.comp (continuous_id.div_const archivedThetaScale).continuousOn ?_
    exact fun t ht => div_pos (mem_Ioi.mp ht) archivedThetaScale_pos
  exact mellin_differentiableAt_of_isBigO_rpow_exp (one_div_pos.mpr archivedThetaScale_pos)
    (hcont.locallyIntegrableOn measurableSet_Ioi) archivedTheta_exponential_decay
    (archivedTheta_center_bound href) hw

theorem archivedMellin_differentiable (href : ArchivedThetaReflects) : Differentiable ℂ archivedMellin := by
  intro w
  by_cases hw : 0 < w.re
  · exact archivedMellin_differentiable_right href hw
  · have hm : 0 < (1-w).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [le_of_not_gt hw]
    have hf := archivedMellin_differentiable_right href hm
    have hmap : DifferentiableAt ℂ (fun z : ℂ => 1-z) w :=
      (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
    have he : archivedMellin ∘ (fun z : ℂ => 1-z) = archivedMellin := funext (archivedMellin_reflects href)
    rw [← he]
    exact hf.comp w hmap

theorem archivedGaussianFactor_differentiable (href : ArchivedThetaReflects) :
    Differentiable ℂ archivedGaussianFactor := by
  have hs : (archivedThetaScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hp : Differentiable ℂ (fun w : ℂ => (archivedThetaScale : ℂ)^w) := fun _ =>
    differentiableAt_id.const_cpow (Or.inl hs)
  exact ((archivedMellin_differentiable href).mul
    (hp.inv (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hs)))).mul Complex.differentiable_one_div_Gamma

theorem archivedFieldContinuation (href : ArchivedThetaReflects) :
    IsDedekindZeta K (fun w => riemannZeta w * chi4.LFunction w * archivedGaussianFactor w) := by
  refine ⟨?_, fun _ hw => (dedekindZeta_eq_archivedGaussianFactor hw).symm⟩
  intro w hw
  have hn : w ≠ 1 := hw
  exact (((differentiableAt_riemannZeta hn).mul (chi4.differentiableAt_LFunction w (Or.inl hn))).mul
    (archivedGaussianFactor_differentiable href w)).differentiableWithinAt

theorem archivedQuarticRH_iff_gaussian
    (href : ArchivedThetaReflects) (hZ : FieldTarget.StripZerosOnLine riemannZeta)
    (hβ : FieldTarget.StripZerosOnLine chi4.LFunction) :
    DedekindZetaRH K ↔ FieldTarget.StripZerosOnLine archivedGaussianFactor :=
  FieldTarget.dedekindZetaRH_iff_third_factor (archivedFieldContinuation href).1
    (archivedFieldContinuation href).2 hZ hβ

#print axioms archivedMellin_reflects
#print axioms archivedGaussianFactor_differentiable
#print axioms archivedFieldContinuation
#print axioms archivedQuarticRH_iff_gaussian

end QuarticModel
