import WeightedContourTaylor
import DedekindDiscriminant23CharacterPanel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Fixed panels for the discriminant-23 Mellin reading at any height. The
Taylor coefficients belong to the theta density, and the weight retains the
exact input to both reflected exponential phases. -/

namespace FieldTarget

open MeasureTheory Metric Set
open scoped Interval NNReal

noncomputable section

def discriminant23PhaseWeight (odd : Bool) (w : ℂ) (u : ℝ) : ℂ :=
  if odd then (u : ℂ) * (Complex.exp (w * u) - Complex.exp ((1 - w) * u))
  else Complex.exp (w * u) + Complex.exp ((1 - w) * u)

/-- The same panels and 20 density coefficients per panel work at all heights. -/
def discriminant23PhaseTaylor (odd : Bool) (w : ℂ) : ℂ :=
  weightedContourTaylorComposite discriminant23PanelDensity
    (discriminant23PhaseWeight odd w) 0 (3 / 64) (1 / 4) 32 20

private theorem density_contour_bound {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 3) {z : ℂ}
    (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) : ‖discriminant23PanelDensity z‖ ≤ 60 := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hi := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  have hcos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith only [(abs_le.mp hi).1, Real.pi_gt_three],
      by linarith only [(abs_le.mp hi).2, Real.pi_gt_three]⟩
  have he : 0 ≤ (Complex.exp z).re := by
    rw [Complex.exp_re]
    exact mul_nonneg (Real.exp_nonneg _) hcos
  have hz₁ : (1 : ℝ) ≤ ‖1 + Complex.exp z‖ := by
    have hp : 1 ≤ ((1 : ℂ) + Complex.exp z).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith only [he]
    exact hp.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have h := (discriminant23_panel_circle_bounds (w := 0) (by norm_num) (by norm_num)
    (by norm_num) hc hz).1
  simp only [discriminant23PanelValue, zero_mul, Complex.exp_zero, sub_zero, one_mul, norm_mul] at h
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hz₁ (norm_nonneg (discriminant23PanelDensity z))).trans h

private theorem phaseWeight_norm_le (odd : Bool) {w : ℂ} {u : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (hu : u ∈ Icc (0 : ℝ) 3) :
    ‖discriminant23PhaseWeight odd w u‖ ≤ if odd then 126 else 42 := by
  have hExp : Real.exp 3 ≤ 21 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _)
      (by linarith only [Real.exp_one_lt_d9] : Real.exp 1 ≤ 68 / 25) 3).trans (by norm_num)
  have hPhase (v : ℂ) (hv : v.re ≤ 1) : ‖Complex.exp (v * (u : ℂ))‖ ≤ 21 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact (Real.exp_le_exp.mpr (by nlinarith only [hu.2, mul_nonneg hu.1 (sub_nonneg.mpr hv)])).trans hExp
  have h₁ := hPhase w hhi
  have h₂ := hPhase (1 - w) (by rw [Complex.sub_re, Complex.one_re]; linarith only [hlo])
  cases odd
  · change ‖Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))‖ ≤ 42
    exact (norm_add_le _ _).trans (by linarith only [h₁, h₂])
  · change ‖(u : ℂ) * (Complex.exp (w * (u : ℂ)) - Complex.exp ((1 - w) * (u : ℂ)))‖ ≤ 126
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    refine (mul_le_mul hu.2 ((norm_sub_le _ _).trans (add_le_add h₁ h₂))
      (norm_nonneg _) (by norm_num)).trans ?_
    norm_num

private theorem phaseTaylor_model_error (odd : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖(∫ u in (0 : ℝ)..3, discriminant23PhaseWeight odd w u * discriminant23PanelDensity (u : ℂ)) -
      discriminant23PhaseTaylor odd w‖ ≤ 1 / 10 ^ 10 := by
  let B : ℝ := if odd then 126 else 42
  have hEnd : (0 : ℝ) + 2 * (32 : ℕ) * (3 / 64) = 3 := by norm_num
  have hDC : Differentiable ℂ discriminant23PanelDensity := by
    unfold discriminant23PanelDensity
    fun_prop
  have hWC : Continuous (discriminant23PhaseWeight odd w) := by
    cases odd
    · change Continuous (fun u : ℝ ↦ Complex.exp (w * u) + Complex.exp ((1 - w) * u))
      fun_prop
    · change Continuous (fun u : ℝ ↦ (u : ℂ) * (Complex.exp (w * u) - Complex.exp ((1 - w) * u)))
      fun_prop
  have hB₀ : 0 ≤ B := by cases odd <;> norm_num [B]
  have hQuad := weightedContourTaylorComposite_error_le (F := discriminant23PanelDensity)
    (W := discriminant23PhaseWeight odd w) (a := 0) (h := 3 / 64) (M := 60) (B := B)
    (R := (1 / 4 : ℝ≥0)) 32 20 (by norm_num) (by norm_num) hDC hWC
    (fun c hc z hz ↦ density_contour_bound (by rwa [hEnd] at hc) hz) hB₀
    (fun u hu ↦ phaseWeight_norm_le odd hlo hhi (by rwa [hEnd] at hu))
  rw [hEnd] at hQuad
  refine hQuad.trans ?_
  cases odd <;> norm_num [B]

theorem discriminant23_phaseTaylor_finite_model_error {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterComplexModel w - discriminant23PhaseTaylor false w‖ ≤ 1 / 10 ^ 10 ∧
    ‖deriv discriminant23CharacterComplexModel w - discriminant23PhaseTaylor true w‖ ≤ 1 / 10 ^ 10 := by
  have hModel : discriminant23CharacterComplexModel w =
      ∫ u in (0 : ℝ)..3, discriminant23PanelValue w (u : ℂ) := by
    simp_rw [discriminant23_panelValue_eq_integrand]
    rfl
  rw [hModel, discriminant23_characterComplexModel_deriv]
  exact ⟨phaseTaylor_model_error false hlo hhi, phaseTaylor_model_error true hlo hhi⟩

theorem discriminant23_phaseTaylor_error {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterFold w - discriminant23PhaseTaylor false w‖ ≤ 11 / 10 ^ 10 ∧
    ‖deriv discriminant23CharacterFold w - discriminant23PhaseTaylor true w‖ ≤ 11 / 10 ^ 10 := by
  have hModel := discriminant23_phaseTaylor_finite_model_error hlo hhi
  have hValue := discriminant23_characterComplexModel_error_sharp (w := w)
    (by linarith only [hlo]) (by linarith only [hhi])
  have hSlope := discriminant23_characterComplexModel_iteratedDeriv_error_sharp 1 hlo hhi
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one] at hSlope
  exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hValue hModel.1).trans (by norm_num)),
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hSlope hModel.2).trans (by norm_num))⟩

end

#print axioms discriminant23_phaseTaylor_finite_model_error
#print axioms discriminant23_phaseTaylor_error

end FieldTarget
