import DedekindMixedThetaClassMass

namespace FieldTarget

open Complex MeasureTheory Set NumberField
open DedekindZetaZeroFree.AbelianQuotient

open private mixedThetaClassRemainder_eq_norm theta_pair_remainder_norm
  from DedekindMixedThetaClassMass

private theorem mixedTheta_remainder_eq_ofReal_norm (K : Type) [Field K] [NumberField K]
    {t : ℝ} (ht : 0 < t) :
    (Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀ =
      (‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ : ℂ) := by
  let P := Theta.mixedThetaPair K
  let S := ∑ c : ClassGroup (𝓞 K), ‖mixedThetaClassRemainder K c t‖
  have hsum : (∑ c : ClassGroup (𝓞 K), mixedThetaClassRemainder K c t) = (S : ℂ) := by
    dsimp only [S]
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun c _ => mixedThetaClassRemainder_eq_norm K c ht
  have he : P.f t - P.f₀ =
      (Theta.alpha K : ℂ) * ∑ c : ClassGroup (𝓞 K), mixedThetaClassRemainder K c t := by
    simp [P, Theta.mixedThetaPair, mixedThetaClassRemainder, Finset.sum_sub_distrib, mul_sub]
  calc
    P.f t - P.f₀ = _ := he
    _ = ((Theta.alpha K * S : ℝ) : ℂ) := by rw [hsum, Complex.ofReal_mul]
    _ = (‖P.f t - P.f₀‖ : ℂ) :=
      congrArg (fun u : ℝ => (u : ℂ)) (theta_pair_remainder_norm K ht).symm

/-- At one, both Mellin weights are real. Their sum is between one and two
on the integration interval. -/
theorem mixedTheta_mass_bracket_from_regularized_one (K : Type) [Field K] [NumberField K] :
    ((Theta.mixedThetaPair K).Λ₀ 1).re ≤
      2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ ∧
    2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ ≤
      2 * ((Theta.mixedThetaPair K).Λ₀ 1).re := by
  let P := Theta.mixedThetaPair K
  let q (t : ℝ) := ‖P.f t - P.f₀‖
  let s (t : ℝ) := (1 + t⁻¹) * q t
  have hAll : IntegrableOn (fun t : ℝ => P.f t - P.f₀) (Ioi 1) := by
    have h := DedekindZetaZeroFree.Hecke.mellinSplitRemainder_f_integrable P
      (Theta.mixedThetaPair_k K) 1
    simpa only [sub_self, cpow_zero, one_mul] using h
  have hq : IntegrableOn q (Ioi 1) := hAll.norm
  have hweight (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) : 1 ≤ 1+t⁻¹ ∧ 1+t⁻¹ ≤ 2 := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hi : t⁻¹ ≤ 1 := by
      rw [← one_div]
      exact (div_le_one ht0).mpr (mem_Ioi.mp ht).le
    exact ⟨le_add_of_nonneg_right (inv_nonneg.mpr ht0.le), by linarith⟩
  have hbounds (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) : q t ≤ s t ∧ s t ≤ 2*q t := by
    have hw := hweight t ht
    have hn : 0 ≤ q t := norm_nonneg _
    exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw.1 hn,
      mul_le_mul_of_nonneg_right hw.2 hn⟩
  have hm : AEStronglyMeasurable s (volume.restrict (Ioi 1)) :=
    (measurable_const.add measurable_id.inv).aestronglyMeasurable.mul hq.aestronglyMeasurable
  have h2 : IntegrableOn (fun t : ℝ => 2*q t) (Ioi 1) := hq.const_mul 2
  have hs : IntegrableOn s (Ioi 1) := by
    apply Integrable.mono' h2 hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hb := hbounds t ht
    rw [Real.norm_of_nonneg ((norm_nonneg _).trans hb.1)]
    exact hb.2
  have hpoint (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) :
      mixedThetaIntegrand K 1 t = (s t : ℂ) := by
    rw [mixedThetaIntegrand, sub_self, Complex.cpow_zero, Complex.cpow_neg_one,
      mixedTheta_remainder_eq_ofReal_norm K (zero_lt_one.trans ht)]
    simp only [s, q, P, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv]
  have hreading : (P.Λ₀ 1).re = ∫ t : ℝ in Ioi 1, s t := by
    change ((Theta.mixedThetaPair K).Λ₀ 1).re = _
    have hcast : (∫ t : ℝ in Ioi 1, (s t : ℂ)) =
        Complex.ofReal (∫ t : ℝ in Ioi 1, s t) := integral_ofReal
    rw [mixedTheta_mellin_eq_integral K,
      setIntegral_congr_fun measurableSet_Ioi hpoint, hcast, Complex.ofReal_re]
  have hUpper : (∫ t : ℝ in Ioi 1, s t) ≤ ∫ t : ℝ in Ioi 1, 2*q t := by
    apply integral_mono_ae hs h2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hbounds t ht).2
  have hLower : (∫ t : ℝ in Ioi 1, q t) ≤ ∫ t : ℝ in Ioi 1, s t := by
    apply integral_mono_ae hq hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hbounds t ht).1
  rw [integral_const_mul] at hUpper
  change (P.Λ₀ 1).re ≤ 2 * (∫ t : ℝ in Ioi 1, q t) ∧
    2 * (∫ t : ℝ in Ioi 1, q t) ≤ 2 * (P.Λ₀ 1).re
  rw [hreading]
  exact ⟨hUpper, mul_le_mul_of_nonneg_left hLower (by norm_num)⟩

/-- An upper bound on one finite real value is enough for the symmetric band. -/
theorem finite_dottie_boundary_of_regularized_one (K : Type) [Field K] [NumberField K]
    {L : ℝ} (hL : 0 ≤ L)
    (hvalue : 2 * ((Theta.mixedThetaPair K).Λ₀ 1).re <
      ‖(Theta.mixedThetaPair K).f₀‖ / (1 + (L + 31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K)
      (-L) L :=
  finite_dottie_boundary_of_mellin_mass K hL
    ((mixedTheta_mass_bracket_from_regularized_one K).2.trans_lt hvalue)

#check @mixedTheta_mass_bracket_from_regularized_one
#check @finite_dottie_boundary_of_regularized_one
#print axioms mixedTheta_mass_bracket_from_regularized_one
#print axioms finite_dottie_boundary_of_regularized_one

end FieldTarget
