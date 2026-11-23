import ArchivedGaussianHalfMellin
import Batteries.Tactic.OpenPrivate

/-! A bound on the completed Gaussian Mellin transform that is uniform
in the imaginary coordinate of the strip needed for the contour shift. -/

open Complex MeasureTheory Set

namespace QuarticModel

open private archivedMellinConvergent_right centeredIntegrand
  mellinIntegrand exp_mellinIntegrand from ArchivedGaussianHalfMellin

private theorem archivedMellin_eq_centered_half_all (v : ℂ) :
    archivedMellin v = ∫ x in Ici (0 : ℝ),
      (2 * (archivedCenteredKernel x : ℂ)) * Complex.cosh ((v-1/2) * (x : ℂ)) := by
  by_cases hv : 0 < v.re
  · exact archivedMellin_eq_centered_half hv
  · have hm : 0 < (1-v).re := by
      simp only [sub_re, one_re]
      linarith [le_of_not_gt hv]
    rw [← archivedMellin_functional_equation v, archivedMellin_eq_centered_half hm]
    refine setIntegral_congr_fun measurableSet_Ici (fun x _ => ?_)
    rw [show (1-v-1/2)*(x : ℂ) = -((v-1/2)*(x : ℂ)) by ring, Complex.cosh_neg]

private theorem norm_cosh_le_exp_abs_re (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le (Complex.exp z) (Complex.exp (-z))
  simp only [Complex.norm_exp, Complex.neg_re] at h
  have hp := Real.exp_le_exp.mpr (le_abs_self z.re)
  have hm := Real.exp_le_exp.mpr (neg_le_abs z.re)
  linarith

private theorem centeredIntegrand_integrable_right {v : ℂ} (hv : 0 < v.re) :
    Integrable (centeredIntegrand v) := by
  have himage : Real.exp '' (univ : Set ℝ) = Ioi 0 := image_univ.trans Real.range_exp
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp x) univ x := (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hi : InjOn Real.exp (univ : Set ℝ) := Real.exp_injective.injOn
  have hInt := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hi
    (mellinIntegrand v)
  rw [himage] at hInt
  simp only [exp_mellinIntegrand, integrableOn_univ] at hInt
  exact hInt.mp (archivedMellinConvergent_right hv)

theorem archivedMellin_strip_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ v : ℂ, |v.re-1/2| ≤ 2 → ‖archivedMellin v‖ ≤ C := by
  let g (x : ℝ) : ℝ := 2 * ‖centeredIntegrand (5/2 : ℂ) x‖
  have hgi : Integrable g :=
    (centeredIntegrand_integrable_right (show 0 < (5/2 : ℂ).re by norm_num)).norm.const_mul 2
  refine ⟨∫ x in Ici 0, g x, integral_nonneg (fun x => by unfold g; positivity), ?_⟩
  intro v hv
  rw [archivedMellin_eq_centered_half_all]
  refine norm_integral_le_of_norm_le hgi.integrableOn ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hxs : 0 ≤ x := hx
  have harg : (((v-1/2)*(x : ℂ)).re) = (v.re-1/2)*x := by
    simp [Complex.mul_re, sub_re]
  have hbound : ‖Complex.cosh ((v-1/2)*(x : ℂ))‖ ≤ Real.exp (2*x) := by
    apply (norm_cosh_le_exp_abs_re _).trans
    rw [harg, abs_mul, abs_of_nonneg hxs, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right hv hxs
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, norm_mul, htwo]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq
  unfold g archivedCenteredKernel centeredIntegrand
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have har : (((5/2 : ℂ)*(x : ℂ)).re) = 5/2*x := by norm_num [Complex.mul_re, Complex.div_ofNat_re]
  rw [har, show 5/2*x = x/2+2*x by ring, Real.exp_add]
  ring

#print axioms archivedMellin_strip_bound

end QuarticModel
