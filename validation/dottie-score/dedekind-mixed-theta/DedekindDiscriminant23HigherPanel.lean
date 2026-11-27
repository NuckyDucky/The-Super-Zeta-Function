import DedekindDiscriminant23CharacterPanel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The original analytic quadrature extends to a higher band with a larger
explicit circle allowance. -/

namespace FieldTarget

open Complex Metric Set
open scoped Interval NNReal

noncomputable section

private theorem panel_xy {c : ℝ} {z : ℂ} (hc : 0 ≤ c)
    (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) :
    -(1 / 4) ≤ z.re ∧ |z.im| ≤ 1 / 4 := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hr := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_eq hd
  have hi := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  exact ⟨by linarith only [(abs_le.mp hr).1, hc], hi⟩

private theorem norm_exp_le_norm_one_add_exp {z : ℂ} (hz : |z.im| ≤ 1 / 4) :
    ‖Complex.exp z‖ ≤ ‖1 + Complex.exp z‖ := by
  have hcos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith only [(abs_le.mp hz).1, Real.pi_gt_three],
      by linarith only [(abs_le.mp hz).2, Real.pi_gt_three]⟩
  have hre : 0 ≤ (Complex.exp z).re := by
    rw [Complex.exp_re]
    exact mul_nonneg (Real.exp_nonneg _) hcos
  have hsq : ‖Complex.exp z‖ ^ 2 ≤ ‖1 + Complex.exp z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, zero_add]
    nlinarith only [hre]
  nlinarith only [hsq, norm_nonneg (Complex.exp z), norm_nonneg ((1 : ℂ) + Complex.exp z)]

private theorem exp_weight_on_panel {w z : ℂ} {T : ℝ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ T) (hx : -(1 / 4) ≤ z.re) (hy : |z.im| ≤ 1 / 4) :
    ‖Complex.exp (w * z)‖ ≤ Real.exp z.re * Real.exp ((1 + T) / 4) := by
  have hReal : w.re * z.re ≤ z.re + 1 / 4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ z.re + 1 / 4 by linarith only [hx]),
      hlo]
  have hImag : -(w.im * z.im) ≤ T / 4 := by
    calc
      _ ≤ |w.im * z.im| := neg_le_abs _
      _ = |w.im| * |z.im| := abs_mul _ _
      _ ≤ T * (1 / 4 : ℝ) := mul_le_mul ht hy (abs_nonneg _)
        ((abs_nonneg w.im).trans ht)
      _ = _ := by ring
  rw [Complex.norm_exp, ← Real.exp_add, Complex.mul_re]
  exact Real.exp_le_exp.mpr (by linarith only [hReal, hImag])

theorem discriminant23_panel_value_bound_at_height {w z : ℂ} {T c : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ T)
    (hc : c ∈ Icc (0 : ℝ) 3) (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) :
    ‖discriminant23PanelValue w z‖ ≤ 120 * Real.exp ((1 + T) / 4) := by
  obtain ⟨hx, hy⟩ := panel_xy hc.1 hz
  have hRef : ‖(1 + Complex.exp z) * discriminant23PanelDensity z‖ ≤ 60 := by
    have h := (discriminant23_panel_circle_bounds (w := 0) (by norm_num) (by norm_num)
      (by norm_num) hc hz).1
    simpa only [discriminant23PanelValue, zero_mul, Complex.exp_zero, sub_zero, one_mul] using h
  have hScaled : Real.exp z.re * ‖discriminant23PanelDensity z‖ ≤ 60 := by
    rw [← Complex.norm_exp z]
    exact (mul_le_mul_of_nonneg_right (norm_exp_le_norm_one_add_exp hy) (norm_nonneg _)).trans
      (by rw [← norm_mul]; exact hRef)
  have hw := exp_weight_on_panel hlo hhi ht hx hy
  have hv := exp_weight_on_panel (w := 1 - w)
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using ht) hx hy
  rw [discriminant23PanelValue, norm_mul]
  calc
    _ ≤ (Real.exp z.re * Real.exp ((1 + T) / 4) +
        Real.exp z.re * Real.exp ((1 + T) / 4)) * ‖discriminant23PanelDensity z‖ :=
      mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hw hv)) (norm_nonneg _)
    _ = (Real.exp z.re * ‖discriminant23PanelDensity z‖) * (2 * Real.exp ((1 + T) / 4)) := by ring
    _ ≤ 60 * (2 * Real.exp ((1 + T) / 4)) :=
      mul_le_mul_of_nonneg_right hScaled (by positivity)
    _ = _ := by ring

theorem discriminant23_value_quadrature_bound_to_six {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 6) :
    ‖discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ 48 / 100000 := by
  have hExpTwo : Real.exp (2 : ℝ) ≤ 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_nonneg (1 : ℝ)]
  have hExp : Real.exp ((1 + (6 : ℝ)) / 4) ≤ 8 :=
    (Real.exp_le_exp.mpr (by norm_num : (1 + (6 : ℝ)) / 4 ≤ 2)).trans hExpTwo
  have hF : Differentiable ℂ (discriminant23PanelValue w) := by
    unfold discriminant23PanelValue discriminant23PanelDensity
    fun_prop
  have h := ninePointComposite_error_le (F := discriminant23PanelValue w) (a := 0)
    (h := 3 / 64) (R := (1 / 4 : ℝ≥0)) (M := 960) 32 (by norm_num) (by norm_num) hF (by
      intro c hc z hz
      have hc' : c ∈ Icc (0 : ℝ) 3 := by convert hc using 1; norm_num
      have hb := discriminant23_panel_value_bound_at_height hlo hhi ht hc' hz
      linarith only [hb, hExp])
  have hModel : discriminant23CharacterComplexModel w =
      ∫ u in (0 : ℝ)..3, discriminant23PanelValue w (u : ℂ) := by
    simp_rw [discriminant23_panelValue_eq_integrand]
    rfl
  rw [hModel]
  norm_num at h ⊢
  exact h.trans (by norm_num)

#print axioms discriminant23_panel_value_bound_at_height
#print axioms discriminant23_value_quadrature_bound_to_six

end

end FieldTarget
