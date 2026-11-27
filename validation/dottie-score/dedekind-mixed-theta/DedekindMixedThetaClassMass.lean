import DedekindMixedThetaPoleDominance

namespace FieldTarget

open Classical Complex MeasureTheory Set NumberField
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.AbelianQuotient
open scoped nonZeroDivisors

noncomputable section

private theorem theta_alpha_pos (K : Type) [Field K] [NumberField K] :
    0 < Theta.alpha K := by
  unfold Theta.alpha
  exact div_pos (mul_pos (by positivity) (regulator_pos K))
    (by exact_mod_cast torsionOrder_pos K)

private theorem radial_remainder_nonneg_real (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (u : Theta.Angular K) :
    ∃ b : ℝ, 0 ≤ b ∧ Theta.mixedRadialTheta K I t u - 1 = (b : ℂ) := by
  let E := NumberField.mixedEmbedding.euclidean.mixedSpace K
  let N := Theta.shapeIdealLattice K I (Theta.mixedThetaShape K I t u)
    (fun v => ne_of_gt (expMapBasis_pos _ v))
  let g (x : N) := Real.exp (-Real.pi * ‖(x : E)‖^2)
  have hs : Summable g := by
    simpa only [g, Function.comp_def, Theta.norm_latticeGaussian] using
      (Theta.summable_latticeGaussian N Real.pi_pos).norm
  have h0 : g (0 : N) = 1 := by simp [g]
  have hb : 1 ≤ ∑' x : N, g x := by
    rw [← h0]
    exact hs.le_tsum _ (fun x _ => (Real.exp_pos _).le)
  refine ⟨(∑' x : N, g x) - 1, sub_nonneg.mpr hb, ?_⟩
  change (∑' x : N, Theta.latticeGaussian Real.pi (x : E)) - 1 = _
  have hg (x : N) : Theta.latticeGaussian Real.pi (x : E) = (g x : ℂ) := by
    simp [Theta.latticeGaussian, g]
  simp_rw [hg]
  rw [← Complex.ofReal_tsum, Complex.ofReal_sub, Complex.ofReal_one]

/-- Remove the zero lattice element in the ideal class used by the mixed theta pair. -/
def mixedThetaClassRemainder (K : Type) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) (t : ℝ) : ℂ :=
  Theta.mixedAngularAverage K
    (FractionalIdeal.mk0 K (Theta.inverseClassIdealRepresentative K c)) t - 1

private theorem mixedThetaClassRemainder_eq_norm (K : Type) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) {t : ℝ} (ht : 0 < t) :
    mixedThetaClassRemainder K c t = (‖mixedThetaClassRemainder K c t‖ : ℂ) := by
  let I := FractionalIdeal.mk0 K (Theta.inverseClassIdealRepresentative K c)
  let q (u : Theta.Angular K) := Theta.mixedRadialTheta K I t u - 1
  have hvalue (u : Theta.Angular K) : q u = ((q u).re : ℂ) := by
    obtain ⟨b, _, hb⟩ := radial_remainder_nonneg_real K I t u
    have hq : q u = (b : ℂ) := hb
    rw [hq, Complex.ofReal_re]
  have hpos (u : Theta.Angular K) : 0 ≤ (q u).re := by
    obtain ⟨b, h, hb⟩ := radial_remainder_nonneg_real K I t u
    simpa [q, hb] using h
  let value := ∫ u in Theta.angularCube K, (q u).re
  have hv : 0 ≤ value := integral_nonneg hpos
  have he : mixedThetaClassRemainder K c t = (value : ℂ) := by
    change Theta.mixedAngularAverage K I t - 1 = (value : ℂ)
    rw [Theta.mixedAngularAverage_sub_one K I t ht]
    exact (congrArg (fun F : Theta.Angular K → ℂ => ∫ u in Theta.angularCube K, F u)
      (funext hvalue)).trans integral_ofReal
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]

private theorem theta_pair_remainder_norm (K : Type) [Field K] [NumberField K]
    {t : ℝ} (ht : 0 < t) :
    ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ =
      Theta.alpha K * ∑ c : ClassGroup (𝓞 K), ‖mixedThetaClassRemainder K c t‖ := by
  have hsum : (∑ c : ClassGroup (𝓞 K), mixedThetaClassRemainder K c t) =
      ((∑ c : ClassGroup (𝓞 K), ‖mixedThetaClassRemainder K c t‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun c _ => mixedThetaClassRemainder_eq_norm K c ht
  have he :
      (Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀ =
        (Theta.alpha K : ℂ) * ∑ c : ClassGroup (𝓞 K), mixedThetaClassRemainder K c t := by
    simp [Theta.mixedThetaPair, mixedThetaClassRemainder, Finset.sum_sub_distrib, mul_sub]
  rw [he, hsum, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (theta_alpha_pos K).le,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

private theorem theta_class_integrable (K : Type) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) :
    IntegrableOn (fun t : ℝ => mixedThetaClassRemainder K c t) (Ioi 1) := by
  let P := Theta.mixedThetaPair K
  let I := FractionalIdeal.mk0 K (Theta.inverseClassIdealRepresentative K c)
  have hAll : IntegrableOn (fun t : ℝ => P.f t - P.f₀) (Ioi 1) := by
    have h := DedekindZetaZeroFree.Hecke.mellinSplitRemainder_f_integrable P
      (Theta.mixedThetaPair_k K) 1
    simpa only [sub_self, cpow_zero, one_mul] using h
  have hdom : IntegrableOn (fun t : ℝ => (Theta.alpha K)⁻¹ * ‖P.f t - P.f₀‖) (Ioi 1) :=
    hAll.norm.const_mul _
  have hl := (Theta.locallyIntegrableOn_mixedAngularAverage K I).mono_set
    (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hm : AEStronglyMeasurable (mixedThetaClassRemainder K c) (volume.restrict (Ioi 1)) :=
    hl.aestronglyMeasurable.sub aestronglyMeasurable_const
  apply Integrable.mono' hdom hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖mixedThetaClassRemainder K c t‖ ≤
    (Theta.alpha K)⁻¹ * ‖P.f t - P.f₀‖
  rw [show ‖P.f t - P.f₀‖ = _ from
    theta_pair_remainder_norm K (zero_lt_one.trans ht),
    ← mul_assoc, inv_mul_cancel₀ (theta_alpha_pos K).ne', one_mul]
  exact Finset.single_le_sum (f := fun d => ‖mixedThetaClassRemainder K d t‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

/-- The contribution of one ideal class to the unscaled absolute theta mass. -/
def mixedThetaClassMass (K : Type) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) : ℝ :=
  ∫ t : ℝ in Ioi 1, ‖mixedThetaClassRemainder K c t‖

/-- The mass splits exactly because every Gaussian remainder is real and nonnegative. -/
theorem mixedTheta_mellin_mass_eq_class_sum (K : Type) [Field K] [NumberField K] :
    2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ =
      Theta.alpha K * (2 * ∑ c : ClassGroup (𝓞 K), mixedThetaClassMass K c) := by
  have hIntegral :
      (∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖) =
        ∫ t : ℝ in Ioi 1, Theta.alpha K *
          ∑ c : ClassGroup (𝓞 K), ‖mixedThetaClassRemainder K c t‖ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact theta_pair_remainder_norm K (zero_lt_one.trans ht)
  rw [hIntegral, integral_const_mul, integral_finsetSum Finset.univ]
  · unfold mixedThetaClassMass
    ring
  · intro c _
    exact (theta_class_integrable K c).norm

private theorem theta_pair_constant_norm (K : Type) [Field K] [NumberField K] :
    ‖(Theta.mixedThetaPair K).f₀‖ =
      Theta.alpha K * (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
  simp [Theta.mixedThetaPair, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (theta_alpha_pos K)]

/-- The factor shared by the theta pair and its pole cancels from the band test. -/
theorem finite_dottie_boundary_of_class_masses (K : Type) [Field K] [NumberField K]
    {L : ℝ} (hL : 0 ≤ L)
    (hmass : 2 * ∑ c : ClassGroup (𝓞 K), mixedThetaClassMass K c <
      (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (1+(L+31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K)
      (-L) L := by
  apply finite_dottie_boundary_of_mellin_mass K hL
  rw [mixedTheta_mellin_mass_eq_class_sum, theta_pair_constant_norm, mul_div_assoc]
  exact mul_lt_mul_of_pos_left hmass (theta_alpha_pos K)

#check @finite_dottie_boundary_of_class_masses
#print axioms mixedTheta_mellin_mass_eq_class_sum
#print axioms finite_dottie_boundary_of_class_masses

end

end FieldTarget
