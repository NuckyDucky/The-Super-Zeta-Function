import QuarticConductorSign

/-! The centered half-Mellin integral used by the ring and quaternion
calculations is the completed Gaussian factor of the actual field. -/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace QuarticModel

private theorem archivedMellinConvergent_right {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (fun t : ℝ => (archivedTheta (t/archivedThetaScale) : ℂ)) w := by
  have hcont : ContinuousOn (fun t : ℝ => (archivedTheta (t/archivedThetaScale) : ℂ)) (Ioi 0) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    refine archivedTheta_continuous_positive.comp (continuous_id.div_const archivedThetaScale).continuousOn ?_
    exact fun t ht => div_pos (mem_Ioi.mp ht) archivedThetaScale_pos
  apply mellinConvergent_of_isBigO_rpow_exp (one_div_pos.mpr archivedThetaScale_pos)
    (hcont.locallyIntegrableOn measurableSet_Ioi) archivedTheta_exponential_decay (b := 0) ?_ hw
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
    Real.norm_eq_abs, archivedTheta_reflection t ht0, abs_mul, abs_of_pos (inv_pos.mpr ht0)]
  calc
    _ ≤ t⁻¹ * (2*Real.exp (-u)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)
    _ = (2*archivedThetaScale)*(u*Real.exp (-u)) := by rw [hscale]; ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hex hs.le

noncomputable def archivedCenteredKernel (x : ℝ) : ℝ :=
  Real.exp (x/2) * archivedTheta (Real.exp x / archivedThetaScale)

private noncomputable def centeredIntegrand (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w * (x : ℂ)) * (archivedTheta (Real.exp x/archivedThetaScale) : ℂ)

private noncomputable def mellinIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)^(w-1) • (archivedTheta (t/archivedThetaScale) : ℂ)

private theorem exp_mellinIntegrand (w : ℂ) (x : ℝ) :
    |Real.exp x| • mellinIntegrand w (Real.exp x) = centeredIntegrand w x := by
  have hx : 0 < Real.exp x := Real.exp_pos x
  simp only [abs_of_pos hx, mellinIntegrand, centeredIntegrand, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Real.log_exp]
  conv_lhs => rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  ring

private theorem integrand_mirror (w : ℂ) (x : ℝ) :
    centeredIntegrand w (-x) = centeredIntegrand (1-w) x := by
  have h := archivedTheta_reflection (Real.exp (-x)) (Real.exp_pos (-x))
  rw [← Real.exp_neg, neg_neg] at h
  simp only [centeredIntegrand, h, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem add_integrands (w : ℂ) (x : ℝ) :
    centeredIntegrand w x + centeredIntegrand (1-w) x =
      (2 * (archivedCenteredKernel x : ℂ)) * Complex.cosh ((w-1/2) * (x : ℂ)) := by
  rw [Complex.cosh, archivedCenteredKernel, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  have h₁ : w * (x : ℂ) = (x : ℂ)/2 + (w-1/2)*(x : ℂ) := by ring
  have h₂ : (1-w) * (x : ℂ) = (x : ℂ)/2 + -((w-1/2)*(x : ℂ)) := by ring
  unfold centeredIntegrand
  rw [h₁, h₂, Complex.exp_add, Complex.exp_add]
  ring

/-- Same integral formula as PinchRadius.halfMellin with the actual theta
kernel. The equality holds throughout the open critical strip. -/
theorem archivedMellin_eq_centered_half {w : ℂ} (hw : 0 < w.re) :
    archivedMellin w = ∫ x in Ici (0 : ℝ),
      (2 * (archivedCenteredKernel x : ℂ)) * Complex.cosh ((w-1/2) * (x : ℂ)) := by
  have himage : Real.exp '' (univ : Set ℝ) = Ioi 0 := image_univ.trans Real.range_exp
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp x) univ x := (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hi : InjOn Real.exp (univ : Set ℝ) := Real.exp_injective.injOn
  have hchange := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hi (mellinIntegrand w)
  rw [himage] at hchange
  simp only [exp_mellinIntegrand] at hchange
  have hInt := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hi (mellinIntegrand w)
  rw [himage] at hInt
  simp only [exp_mellinIntegrand] at hInt
  have hwhole : IntegrableOn (centeredIntegrand w) univ := hInt.mp (archivedMellinConvergent_right hw)
  have hdisj : Disjoint (Ici (0 : ℝ)) (Iio 0) := by
    refine disjoint_left.mpr ?_
    exact fun _ h₁ h₂ => (not_lt_of_ge (mem_Ici.mp h₁)) (mem_Iio.mp h₂)
  have hunion : Ici (0 : ℝ) ∪ Iio 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iio, mem_univ, iff_true]
    exact le_or_gt 0 x
  have hadd := setIntegral_union hdisj measurableSet_Iio
    (hwhole.mono_set (subset_univ _)) (hwhole.mono_set (subset_univ _))
  rw [hunion] at hadd
  have hneg : (fun x : ℝ => -x) '' (Ioi 0) = Iio 0 := by
    ext x
    simp only [mem_image, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact neg_neg_of_pos hz
    · intro hx
      exact ⟨-x,neg_pos.mpr hx,neg_neg x⟩
  have hnd (x : ℝ) (_ : x ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun z : ℝ => -z) (-1) (Ioi 0) x := (hasDerivAt_id x).neg.hasDerivWithinAt
  have hni : InjOn (fun x : ℝ => -x) (Ioi 0) := neg_injective.injOn
  have hflip := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hnd hni (centeredIntegrand w)
  rw [hneg] at hflip
  simp only [abs_neg, abs_one, one_smul, integrand_mirror] at hflip
  have hIflip := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hnd hni
    (centeredIntegrand w)
  rw [hneg] at hIflip
  simp only [abs_neg, abs_one, one_smul, integrand_mirror] at hIflip
  have hI : IntegrableOn (centeredIntegrand (1-w)) (Ici 0) :=
    (hIflip.mp (hwhole.mono_set (subset_univ _))).congr_set_ae Ioi_ae_eq_Ici.symm
  change (∫ t in Ioi 0, mellinIntegrand w t) = _
  rw [hchange, hadd, hflip, setIntegral_congr_set Ioi_ae_eq_Ici, ← integral_add
    (hwhole.mono_set (subset_univ (Ici 0))) hI]
  exact setIntegral_congr_fun measurableSet_Ici (fun x _ => add_integrands w x)

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

/-- The three weights and the quarter-lattice indices in the original
`ReflectedGaussianReading.theta`, written out on this toolchain. -/
theorem archivedTheta_eq_original_quarter {u : ℝ} (hu : 0 < u) :
    archivedTheta u = ∑' p : ℕ × ℕ,
      let m : ℕ := p.1 + 1
      let n := p.2
      ((legendreSym 41 ((m : ℤ) + n*32) * legendreSym 457 ((m : ℤ) + n*109) *
        legendreSym 1414835497 ((m : ℤ) + n*516876951) : ℤ) : ℝ) *
          Real.exp (-((m^2+n^2 : ℕ) : ℝ) * u) := by
  have h := archivedTheta_hasSum_quarter (mul_pos hu archivedThetaScale_pos)
  rw [mul_div_cancel_right₀ _ archivedThetaScale_pos.ne'] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, ← h.tsum_eq]
  apply tsum_congr
  intro p
  dsimp only
  simp only [archivedQuarterWeight, archivedGaussianSign_eq_legendre, archivedQuarterNorm,
    Complex.ofReal_mul, Complex.ofReal_intCast, Nat.cast_add, Nat.cast_one]
  congr 2
  field_simp [archivedThetaScale_pos.ne']

theorem archivedThetaScale_eq_original :
    archivedThetaScale = Real.sqrt (4 * 41 * 457 * 1414835497) / (2 * Real.pi) := by
  rw [archivedThetaScale, show (4 * 41 * 457 * 1414835497 : ℝ) = 4 * 26509772707289 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num]
  ring

#print axioms archivedMellin_eq_centered_half
#print axioms archivedTheta_eq_original_quarter
#print axioms archivedThetaScale_eq_original

end QuarticModel
