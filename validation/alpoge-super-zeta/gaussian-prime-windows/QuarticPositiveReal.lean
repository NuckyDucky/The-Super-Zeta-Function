import QuarticAbelEnvelope
import QuarticCheckedShellKernel
import QuarticMellinFold
import QuarticThetaNormalize
import QuarticRealFormula
import Mathlib.MeasureTheory.Integral.ExpDecay

open Filter MeasureTheory Set

namespace QuarticKernel

/-- The original prefix certificate gives a strictly positive theta kernel
on the entire positive half of the logarithmic axis. -/
theorem certified_kernel_positive {x : ℝ} (hx : 0 ≤ x) : 0 < kernel x :=
  kernel_pos_of_actual_prefix actual_checked_shells_kernel.1 hx

private theorem certified_kernel_even : Function.Even kernel := by
  have h : 0 < theta (1 / scale) := by
    simpa [kernel] using certified_kernel_positive (x := 0) le_rfl
  exact theta_reflection_iff_kernel_even.mp (theta_reflection_of_center_nonzero h.ne')

private theorem all_exponential_weights_integrable (z : ℂ) :
    IntegrableOn (fun x : ℝ => (kernel x : ℂ) * Complex.exp (z * (x : ℂ))) (Ioi 0) := by
  let f : ℝ → ℂ := fun x => (kernel x : ℂ) * Complex.exp (z * (x : ℂ))
  let R : ℝ := max 36 (|z.re| + 2)
  have hR : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 36).trans (le_max_left _ _)
  have hcont : ContinuousOn f (Ici 0) := by
    dsimp only [f]
    have hK := kernel_continuousOn
    fun_prop
  have hcore : IntegrableOn f (Ioc (0 : ℝ) R) :=
    (hcont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) R ⊆ Ici 0)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hsub : Ioi R ⊆ Ici 0 := fun _ hx => hR.trans hx.le
  have hdecay : IntegrableOn (fun x : ℝ => 3 * Real.exp (-x)) (Ioi R) := by
    simpa only [neg_one_mul] using
      (exp_neg_integrableOn_Ioi R (b := 1) one_pos).const_mul (3 : ℝ)
  have htail : IntegrableOn f (Ioi R) := by
    apply hdecay.mono' ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioi)
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [] with x hx
    have hx0 : 0 ≤ x := hsub hx
    have h36 : (36 : ℝ) ≤ x := (le_max_left _ _).trans hx.le
    have h18 : (18 : ℝ) ≤ x := (by norm_num : (18 : ℝ) ≤ 36).trans h36
    have hM : |z.re| + 2 ≤ x := (le_max_right _ _).trans hx.le
    have he : x / 4 ≤ Real.exp ((x - 18) / 2) :=
      (by linarith : x / 4 ≤ (x - 18) / 2 + 1).trans (Real.add_one_le_exp _)
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ x / 4) he 2
    rw [show (Real.exp ((x - 18) / 2)) ^ 2 = Real.exp (x - 18) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring] at hp
    have hfast : (|z.re| + 2) * x ≤ 40 * Real.exp (x - 18) := by
      calc
        _ ≤ x * x := mul_le_mul_of_nonneg_right hM hx0
        _ ≤ _ := by nlinarith [hp, Real.exp_pos (x - 18)]
    have hlin : z.re * x ≤ |z.re| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx0
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (certified_kernel_positive hx0), Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ (3 * Real.exp (x / 2) * Real.exp (-40 * Real.exp (x - 18))) *
          Real.exp (z.re * x) :=
        mul_le_mul_of_nonneg_right (kernel_upper_on_tail h18) (Real.exp_pos _).le
      _ = 3 * Real.exp (x / 2 + -40 * Real.exp (x - 18) + z.re * x) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ 3 * Real.exp (-x) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hfast, hlin, hx0]))
          (by norm_num)
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  exact hcore.union htail

/-- The original completed quartic Mellin reading is strictly positive on
the entire real axis. This uses the prefix certificate and theta reflection. -/
theorem certified_quartic_real_pos (σ : ℝ) :
    0 < (mellin (fun t : ℝ => (theta (t / scale) : ℂ)) (σ : ℂ)).re := by
  let z : ℂ := (σ : ℂ) - 1 / 2
  have hpos := all_exponential_weights_integrable z
  have hneg : IntegrableOn (fun x : ℝ => (kernel x : ℂ) *
      Complex.exp (-(z * (x : ℂ)))) (Ioi 0) := by
    simpa only [neg_mul] using all_exponential_weights_integrable (-z)
  rw [mellin_fold_of_even certified_kernel_even (σ : ℂ) hpos hneg]
  let f : ℝ → ℂ := fun x => (2 * (kernel x : ℂ)) * Complex.cosh (z * (x : ℂ))
  have hf : IntegrableOn f (Ici 0) := by
    apply integrableOn_Ici_iff_integrableOn_Ioi.mpr
    refine (hpos.add hneg).congr ?_
    filter_upwards [] with x
    simp only [f, Complex.cosh, Pi.add_apply]
    ring
  have hreal : z = ((σ - 1 / 2 : ℝ) : ℂ) := by
    simp [z]
  have hRe (x : ℝ) : (f x).re = 2 * kernel x * Real.cosh ((σ - 1 / 2) * x) := by
    dsimp only [f]
    rw [hreal, ← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    norm_cast
  have hposRe (x : ℝ) (hx : 0 ≤ x) : 0 < (f x).re := by
    rw [hRe]
    exact mul_pos (mul_pos (by norm_num) (certified_kernel_positive hx)) (Real.cosh_pos _)
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ici 0)] fun x => (f x).re := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with x hx
    exact (hposRe x hx).le
  change 0 < (∫ x in Ici (0 : ℝ), f x).re
  rw [← RCLike.re_eq_complex_re, ← integral_re hf]
  change 0 < ∫ x in Ici (0 : ℝ), (f x).re
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hf.re]
  have hi : Ioo (0 : ℝ) 1 ⊆ Function.support (fun x => (f x).re) ∩ Ici 0 :=
    fun x hx => ⟨(hposRe x hx.1.le).ne', hx.1.le⟩
  exact (by norm_num [Real.volume_Ioo] : 0 < volume (Ioo (0 : ℝ) 1)).trans_le (measure_mono hi)

private theorem theta_eq_quartic_real_formula {u : ℝ} (hu : 0 < u) :
    theta u = QuarticRealFormula.theta u := by
  rw [theta_quarter_lattice hu, QuarticRealFormula.theta]
  refine tsum_congr fun p => ?_
  simp only [SuperZeta.FieldWeights.conductorReading, jacobiSym.legendreSym.to_jacobiSym]
  push_cast
  congr 2
  ring

/-- The positivity certificate stated with the same explicit Mellin formula
used by the field-side window reduction. -/
theorem certified_quartic_real_formula_pos (σ : ℝ) :
    0 < (QuarticRealFormula.completed (σ : ℂ)).re := by
  have hscale : scale = QuarticRealFormula.scale := by
    norm_num [scale, conductorNorm, QuarticRealFormula.scale]
  have he : mellin (fun t : ℝ => (theta (t / scale) : ℂ)) (σ : ℂ) =
      QuarticRealFormula.completed (σ : ℂ) := by
    unfold QuarticRealFormula.completed mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    dsimp only
    rw [theta_eq_quartic_real_formula (div_pos ht scale_pos), hscale]
  rw [← he]
  exact certified_quartic_real_pos σ

#check certified_quartic_real_pos
#print axioms certified_kernel_positive
#print axioms certified_quartic_real_pos
#print axioms certified_quartic_real_formula_pos

end QuarticKernel
