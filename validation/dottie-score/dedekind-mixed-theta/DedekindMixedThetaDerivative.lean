import ComplexMellinFoldEstimates
import DedekindMixedThetaTail
import DedekindFiniteStripCounts

namespace FieldTarget

open Complex MeasureTheory Set
open scoped Interval
open DedekindZetaZeroFree.AbelianQuotient
open DedekindZetaZeroFree.Hecke

noncomputable section

private def thetaKernel (K : Type) [Field K] [NumberField K] (x : ℝ) : ℂ :=
  (Theta.mixedThetaPair K).f x - (Theta.mixedThetaPair K).f₀

private theorem thetaKernel_power_integrable (K : Type) [Field K] [NumberField K]
    (ρ : ℝ) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (ρ : ℂ) * thetaKernel K x) (Ioi 1) := by
  let P := Theta.mixedThetaPair K
  have h := mellinSplitRemainder_f_integrable P (Theta.mixedThetaPair_k K)
    (1 + (ρ : ℂ))
  simpa only [P, thetaKernel, add_sub_cancel_left] using h

private theorem thetaKernel_integrable (K : Type) [Field K] [NumberField K] :
    IntegrableOn (thetaKernel K) (Ioi 1) := by
  simpa only [Complex.ofReal_zero, cpow_zero, one_mul] using thetaKernel_power_integrable K 0

private theorem thetaKernel_weight_integrable (K : Type) [Field K] [NumberField K]
    (ρ : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ ρ * ‖thetaKernel K x‖) (Ioi 1) := by
  have hNorm : IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ (ρ : ℂ) * thetaKernel K x‖)
      (Ioi 1) := (thetaKernel_power_integrable K ρ).norm
  refine hNorm.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  change ‖(x : ℂ) ^ (ρ : ℂ) * thetaKernel K x‖ = _
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx), Complex.ofReal_re]

private theorem mixedThetaIntegrand_integrable (K : Type) [Field K] [NumberField K]
    (w : ℂ) : IntegrableOn (mixedThetaIntegrand K w) (Ioi 1) := by
  let P := Theta.mixedThetaPair K
  have hk := Theta.mixedThetaPair_k K
  have ha := mellinSplitRemainder_f_integrable P hk w
  have hb := mellinSplitRemainder_g_integrable P hk w
  rw [show P.g = P.f from mixedThetaPair_global_selfDual K,
    show P.g₀ = P.f₀ from mixedThetaPair_global_g₀_eq_f₀ K] at hb
  convert ha.add hb using 1
  funext x
  simp only [mixedThetaIntegrand, add_mul, Pi.add_apply, P]

private theorem mixedThetaTruncation_eq_folded (K : Type) [Field K] [NumberField K]
    {R : ℝ} (hR : 1 ≤ R) :
    mixedThetaTruncation K R = foldedMellinTruncation (thetaKernel K) R := by
  funext w
  apply intervalIntegral.integral_congr
  intro x hx
  have hx₁ : x ∈ Icc (1 : ℝ) R := by rwa [uIcc_of_le hR] at hx
  change _ = foldedMellinWeight w x * _
  rw [foldedMellinWeight_eq_cpow w (zero_lt_one.trans_le hx₁.1)]
  rfl

/-- The finite folded integral is entire for every field and real cutoff. -/
theorem mixedThetaTruncation_differentiable (K : Type) [Field K] [NumberField K]
    {R : ℝ} (hR : 1 ≤ R) : Differentiable ℂ (mixedThetaTruncation K R) := by
  rw [mixedThetaTruncation_eq_folded K hR]
  exact foldedMellinTruncation_differentiable hR
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
      ((thetaKernel_integrable K).mono_set (fun _ hx ↦ hx.1)))

/-- The radial tail weighted for a strip extended by rho on either side. -/
def mixedThetaWeightedTail (K : Type) [Field K] [NumberField K] (R ρ : ℝ) : ℝ :=
  2 * ∫ x : ℝ in Ioi R, x ^ ρ * ‖thetaKernel K x‖

theorem mixedTheta_mellin_error_le_wide (K : Type) [Field K] [NumberField K]
    {R ρ : ℝ} (hR : 1 ≤ R) (w : ℂ) (hlo : -ρ ≤ w.re) (hhi : w.re ≤ 1 + ρ) :
    ‖(Theta.mixedThetaPair K).Λ₀ w - mixedThetaTruncation K R w‖ ≤
      mixedThetaWeightedTail K R ρ := by
  have hf := mixedThetaIntegrand_integrable K w
  have hTail := hf.mono_set (Ioi_subset_Ioi hR)
  rw [mixedTheta_mellin_eq_integral, ← intervalIntegral.integral_interval_add_Ioi hf hTail,
    mixedThetaTruncation, add_sub_cancel_left]
  let M (x : ℝ) := 2 * (x ^ ρ * ‖thetaKernel K x‖)
  have hM : IntegrableOn M (Ioi R) :=
    ((thetaKernel_weight_integrable K ρ).mono_set (Ioi_subset_Ioi hR)).const_mul 2
  have hBound := norm_integral_le_of_norm_le (f := mixedThetaIntegrand K w) hM
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      have hx₁ : 1 ≤ x := hR.trans hx.le
      change ‖((x : ℂ) ^ (w - 1) + (x : ℂ) ^ (-w)) * thetaKernel K x‖ ≤ _
      rw [← foldedMellinWeight_eq_cpow w (zero_lt_one.trans_le hx₁), norm_mul]
      exact (mul_le_mul_of_nonneg_right (foldedMellinWeight_norm_le hx₁ hlo hhi)
        (norm_nonneg _)).trans_eq (mul_assoc _ _ _))
  simpa only [M, mixedThetaWeightedTail, integral_const_mul] using hBound

/-- A single weighted radial tail bounds every complex derivative of the
actual folded reading on the full closed strip. -/
theorem mixedTheta_mellin_iteratedDeriv_error_le (K : Type) [Field K] [NumberField K]
    (n : ℕ) {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ)
    {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖iteratedDeriv n (Theta.mixedThetaPair K).Λ₀ w -
        iteratedDeriv n (mixedThetaTruncation K R) w‖ ≤
      n.factorial * mixedThetaWeightedTail K R ρ / ρ ^ n :=
  iteratedDeriv_error_le_of_strip (Theta.mixedThetaPair K).differentiable_Λ₀
    (mixedThetaTruncation_differentiable K hR) n hρ
    (fun z ↦ mixedTheta_mellin_error_le_wide K hR z) hlo hhi

#check @mixedTheta_mellin_error_le_wide
#check @mixedTheta_mellin_iteratedDeriv_error_le
#print axioms mixedThetaTruncation_differentiable
#print axioms mixedTheta_mellin_error_le_wide
#print axioms mixedTheta_mellin_iteratedDeriv_error_le

end
end FieldTarget
