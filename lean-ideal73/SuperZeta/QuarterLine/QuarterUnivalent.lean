import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace SuperZeta.QuarterUnivalent
noncomputable section
open Set Complex

/-- The real part of a complex secant slope equals the real part of the
derivative at an interior point of that particular segment. -/
theorem secant_real_eq {D : Set ℂ} {F : ℂ → ℂ}
    (hc : Convex ℝ D) (hf : ∀ z ∈ D, DifferentiableAt ℂ F z)
    {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) :
    ∃ t ∈ Ioo (0:ℝ) 1, ((F y-F x)/(y-x)).re = (deriv F (x+t • (y-x))).re := by
  let d := y-x
  let γ (u : ℂ) := x+u*d
  let g (u : ℝ) := ((F (γ u) - F x)/d).re
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have mem {t : ℝ} (ht : t ∈ Icc 0 1) : γ t ∈ D := by
    simpa only [γ, d, Complex.real_smul] using hc.add_smul_sub_mem hx hy ht
  have dγ (t : ℝ) : HasDerivAt γ d (t:ℂ) := by
    simpa [γ] using (((hasDerivAt_id (t:ℂ)).mul_const d).const_add x)
  have dg {t : ℝ} (ht : t ∈ Icc 0 1) : HasDerivAt g (deriv F (γ t)).re t := by
    have h := ((((hf _ (mem ht)).hasDerivAt.comp (t:ℂ) (dγ t)).sub_const (F x)).div_const d).real_of_complex
    simpa [g, Function.comp_def, hd] using h
  obtain ⟨t,ht,h⟩ := exists_hasDerivAt_eq_slope g (fun t => (deriv F (γ t)).re)
    (show (0:ℝ)<1 by norm_num)
    (fun t ht => (dg ht).continuousAt.continuousWithinAt) (fun t ht => dg ⟨ht.1.le,ht.2.le⟩)
  refine ⟨t,ht,?_⟩
  simpa [g, γ, d, Complex.real_smul] using h.symm

/-- A holomorphic map with negative real derivative part is injective on any
convex region on which this strict inequality holds. -/
theorem injOn_of_deriv_re_neg {D : Set ℂ} {F : ℂ → ℂ}
    (hc : Convex ℝ D) (hf : ∀ z ∈ D, DifferentiableAt ℂ F z)
    (hn : ∀ z ∈ D, (deriv F z).re < 0) : InjOn F D := by
  intro x hx y hy heq
  by_contra hne
  obtain ⟨t,ht,h⟩ := secant_real_eq hc hf hx hy hne
  have hm := hn _ (hc.add_smul_sub_mem hx hy ⟨ht.1.le,ht.2.le⟩)
  simpa [heq] using h.trans_lt hm

/-- A uniform derivative margin bounds how closely the images of two distinct
inputs can approach, even when the inputs differ in both coordinates. -/
theorem image_separation {D : Set ℂ} {F : ℂ → ℂ} {κ : ℝ}
    (hc : Convex ℝ D) (hf : ∀ z ∈ D, DifferentiableAt ℂ F z)
    (hn : ∀ z ∈ D, (deriv F z).re < -κ) {x y : ℂ}
    (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) :
    κ * ‖y-x‖ < ‖F y-F x‖ := by
  obtain ⟨t,ht,h⟩ := secant_real_eq hc hf hx hy hne
  have hm := hn _ (hc.add_smul_sub_mem hx hy ⟨ht.1.le,ht.2.le⟩)
  have hsec : κ < ‖(F y-F x)/(y-x)‖ := by
    linarith [neg_abs_le ((F y-F x)/(y-x)).re, Complex.abs_re_le_norm ((F y-F x)/(y-x))]
  rwa [norm_div, lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))] at hsec

end
end SuperZeta.QuarterUnivalent
