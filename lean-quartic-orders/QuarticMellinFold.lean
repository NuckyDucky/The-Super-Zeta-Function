import QuarticMellin
import QuarticIntegrable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set

namespace QuarticKernel

theorem mellin_log (s : ℂ) :
    mellin (fun t : ℝ => (theta (t/scale) : ℂ)) s =
      ∫ x : ℝ, (kernel x : ℂ) * Complex.exp ((s-1/2)*(x : ℂ)) := by
  unfold mellin
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ)^(s-1) • (theta (t/scale) : ℂ))
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [abs_of_pos (Real.exp_pos x), Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [kernel, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  rw [← mul_assoc, ← Complex.exp_add, mul_right_comm, mul_assoc, ← mul_assoc,
    ← Complex.exp_add]
  congr 1
  ring

theorem theta_reflection_iff_kernel_even :
    (∀ t : ℝ, 0 < t → theta (t/scale) = t⁻¹ * theta (t⁻¹/scale)) ↔
      Function.Even kernel := by
  constructor
  · intro h x
    have ht := h (Real.exp x) (Real.exp_pos x)
    unfold kernel
    rw [ht, ← Real.exp_neg, ← mul_assoc, ← Real.exp_add]
    rw [show x/2 + -x = -x/2 by ring]
  · intro h t ht
    calc
      theta (t/scale) = (Real.exp (Real.log t/2))⁻¹ * kernel (Real.log t) := by
        unfold kernel
        rw [Real.exp_log ht]
        field_simp [(Real.exp_pos (Real.log t/2)).ne']
      _ = t⁻¹ * theta (t⁻¹/scale) := by
        rw [← h (Real.log t), ← Real.exp_neg]
        unfold kernel
        rw [Real.exp_neg (Real.log t), Real.exp_log ht, ← mul_assoc, ← Real.exp_add,
          show -(Real.log t/2) + -Real.log t/2 = -Real.log t by ring,
          Real.exp_neg, Real.exp_log ht]

theorem mellin_fold_of_even (hK : Function.Even kernel) (s : ℂ)
    (hpos : IntegrableOn (fun x : ℝ =>
      (kernel x : ℂ) * Complex.exp ((s-1/2)*(x : ℂ))) (Ioi 0))
    (hneg : IntegrableOn (fun x : ℝ =>
      (kernel x : ℂ) * Complex.exp (-((s-1/2)*(x : ℂ)))) (Ioi 0)) :
    mellin (fun t : ℝ => (theta (t/scale) : ℂ)) s =
      SuperZeta.PinchRadius.halfMellin kernel (s-1/2) := by
  let f : ℝ → ℂ := fun x => (kernel x : ℂ) * Complex.exp ((s-1/2)*(x : ℂ))
  have hfn (x : ℝ) : f (-x) = (kernel x : ℂ) * Complex.exp (-((s-1/2)*(x : ℂ))) := by
    simp only [f, hK x, Complex.ofReal_neg, mul_neg]
  have hleft : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, hfn, neg_preimage, neg_Iic, neg_zero]
    exact integrableOn_Ici_iff_integrableOn_Ioi.mpr hneg
  rw [mellin_log]
  change (∫ x, f x) = _
  have hsplit := setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hpos
  rw [Iic_union_Ioi, Measure.restrict_univ] at hsplit
  rw [hsplit]
  have hflip : (∫ x in Iic (0:ℝ), f x) = ∫ x in Ioi (0:ℝ), f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0:ℝ) f).symm
  have hn : IntegrableOn (fun x => f (-x)) (Ioi (0:ℝ)) := by
    simp_rw [hfn]
    exact hneg
  rw [hflip, ← integral_add hn hpos, SuperZeta.PinchRadius.halfMellin,
    integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [hfn]
  simp only [f, Complex.cosh]
  ring

theorem exponential_kernel_integrable {z : ℂ} (hz : |z.re| ≤ 1/20) :
    IntegrableOn (fun x : ℝ => (kernel x : ℂ) * Complex.exp (z * (x : ℂ))) (Ioi 0) := by
  let f : ℝ → ℂ := fun x => (kernel x : ℂ) * Complex.exp (z * (x : ℂ))
  have hc : ContinuousOn f (Ici 0) := by
    dsimp only [f]
    have hK := kernel_continuousOn
    fun_prop
  have hcore : IntegrableOn f (Ioc (0:ℝ) 18) :=
    (hc.mono (Icc_subset_Ici_self : Icc (0:ℝ) 18 ⊆ Ici 0)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hsub : Ioi (18:ℝ) ⊆ Ici 0 := fun x hx => by
    exact (by norm_num : (0:ℝ) ≤ 18).trans hx.le
  have htail : IntegrableOn f (Ioi 18) := by
    apply weighted_tail.1.mono' ((hc.mono hsub).aestronglyMeasurable measurableSet_Ioi)
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [] with x hx
    have hx0 := hsub hx
    have hk := (kernel_pos_on_tail hx.le).le
    have he : (z * (x:ℂ)).re ≤ x/20 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      linarith only [mul_le_mul_of_nonneg_right ((le_abs_self z.re).trans hz) hx0]
    have hx2 : (1:ℝ) ≤ x^2 := by
      have hb : 1 ≤ x := by linarith [mem_Ioi.mp hx]
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb 2
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk, Complex.norm_exp]
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hk).trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hk (sub_nonneg.mpr hx2)])
      (Real.exp_pos _).le
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 18)]
  exact hcore.union htail

theorem mellin_fold_in_rectangle (hK : Function.Even kernel) (a t : ℝ) (ha : |a| ≤ 1/20) :
    mellin (fun x : ℝ => (theta (x/scale) : ℂ)) (GaussianSideSign.point a t) =
      SuperZeta.PinchRadius.halfMellin kernel ⟨a,t⟩ := by
  have hz : GaussianSideSign.point a t - 1/2 = (⟨a,t⟩ : ℂ) := by
    apply Complex.ext <;> simp [GaussianSideSign.point, Complex.div_re]
  rw [← hz]
  apply mellin_fold_of_even hK
  · rw [hz]
    exact exponential_kernel_integrable ha
  · rw [hz]
    simp only [← neg_mul]
    apply exponential_kernel_integrable
    simpa only [Complex.neg_re, abs_neg] using ha

#print axioms mellin_log
#print axioms theta_reflection_iff_kernel_even
#print axioms mellin_fold_of_even
#print axioms exponential_kernel_integrable
#print axioms mellin_fold_in_rectangle

end QuarticKernel
