import QuarticKernel
import GaussianSideSign
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set MeasureTheory

namespace QuarticKernel

noncomputable def mass (x : ℝ) : ℝ := 2*kernel x*x^2

private noncomputable def envelope (x : ℝ) : ℝ := |mass x| * Real.exp (x/20)

private theorem tail_restrict : Ioi (18 : ℝ) ⊆ Ici 0 := fun x hx => by
  rw [mem_Ici]
  linarith [mem_Ioi.mp hx]

private theorem core_restrict : Icc (0 : ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1

private theorem envelope_integrable : IntegrableOn envelope (Ici 0) := by
  rw [← Icc_union_Ioi_eq_Ici (by norm_num : (0:ℝ) ≤ 18)]
  have hK := kernel_continuousOn.mono core_restrict
  have hc : ContinuousOn envelope (Icc (0:ℝ) 18) := by
    unfold envelope mass
    fun_prop
  have hi : IntegrableOn envelope (Ioi 18) := by
    refine IntegrableOn.congr_fun weighted_tail.1 ?_ measurableSet_Ioi
    intro x hx
    simp only [envelope, mass, abs_of_nonneg
      (show 0 ≤ 2*kernel x*x^2 by have := kernel_pos_on_tail hx.le; positivity)]
  exact hc.integrableOn_Icc.union hi

private theorem mass_measurable :
    AEStronglyMeasurable mass (volume.restrict (Ici 0)) := by
  have hK := kernel_continuousOn
  have h : ContinuousOn mass (Ici 0) := by
    unfold mass
    fun_prop
  exact h.aestronglyMeasurable measurableSet_Ici

theorem mass_integrable : IntegrableOn mass (Ici 0) := by
  refine envelope_integrable.mono' mass_measurable ?_
  apply (ae_restrict_iff' measurableSet_Ici).mpr
  filter_upwards [] with x hx
  rw [Real.norm_eq_abs, envelope]
  simpa using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by
    have h : 0 ≤ x := hx
    linarith : 0 ≤ x/20)) (abs_nonneg (mass x))

private theorem measurable_sinc : Measurable GaussianSideIntegral.sinc := by
  unfold GaussianSideIntegral.sinc
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Real.continuous_sin.measurable.div measurable_id)

private theorem measurable_sinhc : Measurable GaussianSideIntegral.sinhc := by
  unfold GaussianSideIntegral.sinhc
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Real.continuous_sinh.measurable.div measurable_id)

theorem sinc_mass_integrable (t : ℝ) :
    IntegrableOn (fun x => mass x * GaussianSideIntegral.sinc (t*x)) (Ici 0) := by
  have h : Measurable (fun x : ℝ => GaussianSideIntegral.sinc (t*x)) :=
    measurable_sinc.comp (measurable_const.mul measurable_id)
  refine mass_integrable.abs.mono' (mass_measurable.mul h.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (GaussianSideIntegral.sinc (t*x))]
  simpa using mul_le_mul_of_nonneg_left (GaussianSideIntegral.abs_sinc_le_one (t*x)) (abs_nonneg (mass x))

theorem sinhc_sinc_mass_integrable {a : ℝ} (ha : |a| ≤ 1/20) (t : ℝ) :
    IntegrableOn (fun x => mass x * GaussianSideIntegral.sinc (t*x) *
      GaussianSideIntegral.sinhc (a*x)) (Ici 0) := by
  have h : Measurable (fun x : ℝ => GaussianSideIntegral.sinc (t*x)) :=
    measurable_sinc.comp (measurable_const.mul measurable_id)
  have hc : Measurable (fun x : ℝ => GaussianSideIntegral.sinhc (a*x)) :=
    measurable_sinhc.comp (measurable_const.mul measurable_id)
  refine envelope_integrable.mono' ((mass_measurable.mul h.aestronglyMeasurable).mul
    hc.aestronglyMeasurable) ?_
  apply (ae_restrict_iff' measurableSet_Ici).mpr
  filter_upwards [] with x hx
  have hx0 : 0 ≤ x := hx
  have hco : GaussianSideIntegral.sinhc (a*x) = GaussianSideError.averageCosh (a*x) :=
    (GaussianSideError.averageCosh_eq (a*x)).symm
  have hco₀ : 0 ≤ GaussianSideError.averageCosh (a*x) :=
    zero_le_one.trans (GaussianSideError.one_le_averageCosh _)
  have hx' : |a*x| ≤ x/20 := by
    rw [abs_mul, abs_of_nonneg hx0]
    linarith [mul_le_mul_of_nonneg_right ha hx0]
  have hco₁ := (GaussianSideError.averageCosh_le_exp_abs (a*x)).trans (Real.exp_le_exp.mpr hx')
  rw [Real.norm_eq_abs, abs_mul, abs_mul, hco, abs_of_nonneg hco₀, envelope]
  have hs := GaussianSideIntegral.abs_sinc_le_one (t*x)
  calc
    _ ≤ (|mass x| * 1) * Real.exp (x/20) := by gcongr
    _ = _ := by rw [mul_one]

private theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  unfold Complex.cosh
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  refine (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num : (0:ℝ) ≤ 2)).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  have h₁ := Real.exp_le_exp.mpr (le_abs_self z.re)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs z.re)
  linarith

private noncomputable def integrand (a t x : ℝ) : ℂ :=
  (2 * (kernel x : ℂ)) * Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))

private theorem integrand_continuous {s : Set ℝ} (hK : ContinuousOn kernel s) (a t : ℝ) :
    ContinuousOn (integrand a t) s := by
  unfold integrand
  have hf : Continuous (fun x : ℝ => Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))) :=
    Complex.continuous_cosh.comp ((continuous_const : Continuous (fun _ : ℝ => (⟨a,t⟩ : ℂ))).mul
      Complex.continuous_ofReal)
  exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hK)).mul hf.continuousOn

private theorem integrand_le_tail {a : ℝ} (ha : |a| ≤ 1/20) (t : ℝ) {x : ℝ} (hx : 18 < x) :
    ‖integrand a t x‖ ≤ (2*kernel x*x^2) * Real.exp (x/20) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hK := (kernel_pos_on_tail hx.le).le
  have hr : ((⟨a,t⟩ : ℂ) * (x : ℂ)).re = a*x := by simp [Complex.mul_re]
  have harg : |((⟨a,t⟩ : ℂ) * (x : ℂ)).re| ≤ x/20 := by
    rw [hr, abs_mul, abs_of_nonneg hx0]
    linarith only [mul_le_mul_of_nonneg_right ha hx0]
  have hg := (norm_cosh_le ((⟨a,t⟩ : ℂ) * (x : ℂ))).trans (Real.exp_le_exp.mpr harg)
  unfold integrand
  rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  have hx2 : (1:ℝ) ≤ x^2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hx] : 1 ≤ x) 2
  have hmass : 0 ≤ 2*kernel x := mul_nonneg (by norm_num) hK
  exact (mul_le_mul_of_nonneg_left hg hmass).trans
    (mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hx2 hmass)
      (Real.exp_pos _).le)

private theorem integrable_integrand {a : ℝ} (ha : |a| ≤ 1/20) (t : ℝ) :
    IntegrableOn (integrand a t) (Ici 0) := by
  have hc₁ := integrand_continuous (kernel_continuousOn.mono core_restrict) a t
  have hc₂ := integrand_continuous (kernel_continuousOn.mono tail_restrict) a t
  have htail : IntegrableOn (integrand a t) (Ioi 18) := by
    refine weighted_tail.1.mono' (hc₂.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => integrand_le_tail ha t hx)
  rw [← Icc_union_Ioi_eq_Ici (by norm_num : (0:ℝ) ≤ 18)]
  exact hc₁.integrableOn_Icc.union htail

theorem complex_integrable {a : ℝ} (ha : |a| ≤ 1/20) (t : ℝ) :
    IntegrableOn (fun x : ℝ => (2 * (kernel x : ℂ)) *
      Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))) (Ici 0) := by
  simpa only [integrand] using integrable_integrand ha t

#print axioms mass_integrable
#print axioms sinc_mass_integrable
#print axioms sinhc_sinc_mass_integrable
#print axioms complex_integrable

end QuarticKernel
