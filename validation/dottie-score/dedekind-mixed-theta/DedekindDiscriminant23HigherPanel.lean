import DedekindDiscriminant23CharacterPanel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The original analytic quadrature extends to a higher band with a larger
explicit circle allowance. -/

namespace FieldTarget

open Complex Metric Set
open scoped Interval NNReal

noncomputable section

private theorem panel_xy {c R : ℝ} {z : ℂ} (hc : 0 ≤ c)
    (hz : z ∈ sphere (c : ℂ) R) :
    -R ≤ z.re ∧ |z.im| ≤ R := by
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

private theorem exp_weight_on_panel {w z : ℂ} {T R : ℝ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ T) (hx : -R ≤ z.re) (hy : |z.im| ≤ R) :
    ‖Complex.exp (w * z)‖ ≤ Real.exp z.re * Real.exp ((1 + T) * R) := by
  have hReal : w.re * z.re ≤ z.re + R := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ z.re + R by linarith only [hx]),
      mul_nonneg hlo ((abs_nonneg z.im).trans hy),
      hlo]
  have hImag : -(w.im * z.im) ≤ T * R := by
    calc
      _ ≤ |w.im * z.im| := neg_le_abs _
      _ = |w.im| * |z.im| := abs_mul _ _
      _ ≤ T * R := mul_le_mul ht hy (abs_nonneg _)
        ((abs_nonneg w.im).trans ht)
  rw [Complex.norm_exp, ← Real.exp_add, Complex.mul_re]
  exact Real.exp_le_exp.mpr (by nlinarith only [hReal, hImag])

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
  have hRadius : (1 + T) * (1 / 4 : ℝ) = (1 + T) / 4 := by ring
  rw [hRadius] at hw hv
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

private theorem wider_panel_density_bound {z : ℂ} (hx : -(1 / 2) ≤ z.re)
    (hy : |z.im| ≤ 1 / 2) :
    Real.exp z.re * ‖discriminant23PanelDensity z‖ ≤ 9 / 4 := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hCos : (7 / 8 : ℝ) ≤ Real.cos z.im := by
    have hSq : z.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith only [hSq, Real.one_sub_sq_div_two_le_cos (x := z.im)]
  have hScale : 1 ≤ discriminant23ThetaScale * Real.cos z.im :=
    (by norm_num : (1 : ℝ) ≤ (13 / 10) * (7 / 8)).trans
      (mul_le_mul discriminant23_thetaScale_interval.1 hCos (by norm_num)
        (by linarith only [discriminant23_thetaScale_interval.1]))
  have hHeat : ‖q‖ ≤ Real.exp (-Real.exp z.re) := by
    dsimp only [q]
    rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.exp_re]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hScale (Real.exp_nonneg z.re)
    linarith only [hm, mul_one (Real.exp z.re), one_mul (Real.exp z.re),
      mul_assoc discriminant23ThetaScale (Real.exp z.re) (Real.cos z.im),
      mul_comm (Real.exp z.re) (Real.cos z.im)]
  have hHeatUpper : ‖q‖ ≤ 2 / 3 := by
    refine hHeat.trans ((Real.exp_le_exp.mpr (show -Real.exp z.re ≤ -(1 / 2) by
      linarith only [Real.add_one_le_exp z.re, hx])).trans ?_)
    rw [Real.exp_neg, ← one_div, show (2 / 3 : ℝ) = 1 / (3 / 2) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith only [Real.add_one_le_exp (1 / 2 : ℝ)])
  have hGeomRat : ∑ n ∈ Finset.range 32, (2 : ℚ) * (2 / 3 : ℚ) ^ n ≤ 6 := by decide +kernel
  have hGeom : ∑ n ∈ Finset.range 32, (2 : ℝ) * (2 / 3 : ℝ) ^ n ≤ 6 := by
    have hReal : ((∑ n ∈ Finset.range 32, (2 : ℚ) * (2 / 3 : ℚ) ^ n : ℚ) : ℝ) ≤
        ((6 : ℚ) : ℝ) := Rat.cast_le.mpr hGeomRat
    push_cast at hReal
    exact hReal
  have hScaledHeat : Real.exp z.re * ‖q‖ ≤ 3 / 8 := by
    have h := Real.add_one_le_exp (Real.exp z.re - 1)
    have hMul := mul_le_mul_of_nonneg_right
      (show Real.exp z.re ≤ Real.exp (Real.exp z.re - 1) by linarith only [h])
      (Real.exp_nonneg (-Real.exp z.re))
    have hProduct :
        Real.exp (Real.exp z.re - 1) * Real.exp (-Real.exp z.re) = Real.exp (-1) := by
      rw [← Real.exp_add, show Real.exp z.re - 1 + -Real.exp z.re = -1 by ring]
    rw [hProduct] at hMul
    have hNeg : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
      rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.exp_one_gt_d9])
    exact (mul_le_mul_of_nonneg_left hHeat (Real.exp_nonneg _)).trans (hMul.trans hNeg)
  refine (mul_le_mul_of_nonneg_left
    (discriminant23_panel_density_norm_le_of_geometric_bound hHeatUpper hGeom)
    (Real.exp_nonneg _)).trans ?_
  linarith only [mul_le_mul_of_nonneg_left hScaledHeat (by norm_num : (0 : ℝ) ≤ 6),
    mul_comm (Real.exp z.re) 6, mul_assoc 6 (Real.exp z.re) ‖q‖]

private theorem wider_panel_circle_bounds {w z : ℂ} {c : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 8)
    (hc : c ∈ Icc (0 : ℝ) 3) (hz : z ∈ sphere (c : ℂ) (1 / 2 : ℝ)) :
    ‖discriminant23PanelValue w z‖ ≤ 2400 ∧ ‖discriminant23PanelSlope w z‖ ≤ 2400 := by
  obtain ⟨hx, hy⟩ := panel_xy hc.1 hz
  have hn : ‖z‖ ≤ 7 / 2 := by
    have hd := mem_sphere.mp hz
    rw [dist_eq_norm] at hd
    have hh := norm_add_le (z - (c : ℂ)) (c : ℂ)
    rw [sub_add_cancel, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1] at hh
    linarith only [hh, hc.2]
  have hExp : Real.exp ((1 + (8 : ℝ)) * (1 / 2)) ≤ 150 := by
    refine (Real.exp_le_exp.mpr (by norm_num : (1 + (8 : ℝ)) * (1 / 2) ≤ 5)).trans ?_
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _)
      (by linarith only [Real.exp_one_lt_d9] : Real.exp 1 ≤ 68 / 25) 5).trans (by norm_num)
  have hTerm (v : ℂ) (hL : 0 ≤ v.re) (hH : v.re ≤ 1) (hT : |v.im| ≤ 8) :
      ‖Complex.exp (v * z) * discriminant23PanelDensity z‖ ≤ 675 / 2 := by
    rw [norm_mul]
    calc
      _ ≤ (Real.exp z.re * Real.exp ((1 + (8 : ℝ)) * (1 / 2))) *
          ‖discriminant23PanelDensity z‖ :=
        mul_le_mul_of_nonneg_right (exp_weight_on_panel hL hH hT hx hy) (norm_nonneg _)
      _ = (Real.exp z.re * ‖discriminant23PanelDensity z‖) *
          Real.exp ((1 + (8 : ℝ)) * (1 / 2)) := by ring
      _ ≤ (9 / 4 : ℝ) * 150 :=
        mul_le_mul (wider_panel_density_bound hx hy) hExp (Real.exp_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hw := hTerm w hlo hhi ht
  have hv := hTerm (1 - w)
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using ht)
  constructor
  · rw [discriminant23PanelValue, add_mul]
    exact (norm_add_le _ _).trans (by linarith only [hw, hv])
  · rw [discriminant23PanelSlope, mul_assoc, sub_mul, norm_mul]
    have hsub := (norm_sub_le _ _).trans (add_le_add hw hv)
    exact (mul_le_mul hn hsub (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem discriminant23_character_quadrature_bounds_to_eight {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 8) :
    ‖discriminant23CharacterComplexModel w -
        ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ 11 / 10 ^ 7 ∧
    ‖deriv discriminant23CharacterComplexModel w -
        ninePointComposite (fun u ↦ discriminant23PanelSlope w u) 0 (3 / 64) 32‖ ≤ 11 / 10 ^ 7 := by
  have hAny {F : ℂ → ℂ} (hF : Differentiable ℂ F)
      (hB : ∀ c ∈ Icc (0 : ℝ) 3, ∀ z ∈ sphere (c : ℂ) (1 / 2 : ℝ), ‖F z‖ ≤ 2400) :
      ‖(∫ u in (0 : ℝ)..3, F (u : ℂ)) -
        ninePointComposite (fun u ↦ F u) 0 (3 / 64) 32‖ ≤ 11 / 10 ^ 7 := by
    have h := ninePointComposite_error_le (F := F) (a := 0) (h := 3 / 64)
      (R := (1 / 2 : ℝ≥0)) (M := 2400) 32 (by norm_num) (by norm_num) hF (by
        intro c hc z hz
        exact hB c (by convert hc using 1; norm_num) z hz)
    norm_num at h ⊢
    exact h.trans (by norm_num)
  have hModel : discriminant23CharacterComplexModel w =
      ∫ u in (0 : ℝ)..3, discriminant23PanelValue w (u : ℂ) := by
    simp_rw [discriminant23_panelValue_eq_integrand]
    rfl
  rw [hModel, discriminant23_characterComplexModel_deriv]
  exact ⟨hAny (by unfold discriminant23PanelValue discriminant23PanelDensity; fun_prop)
      (fun _ hc _ hz ↦ (wider_panel_circle_bounds hlo hhi ht hc hz).1),
    hAny (by unfold discriminant23PanelSlope discriminant23PanelDensity; fun_prop)
      (fun _ hc _ hz ↦ (wider_panel_circle_bounds hlo hhi ht hc hz).2)⟩

private theorem panel_density_bound_three_quarters {z : ℂ} (hx : -(3 / 4 : ℝ) ≤ z.re)
    (hy : |z.im| ≤ 3 / 4) :
    Real.exp z.re * ‖discriminant23PanelDensity z‖ ≤ 5 := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hCos : (23 / 32 : ℝ) ≤ Real.cos z.im := by
    have hSq : z.im ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith only [hSq, Real.one_sub_sq_div_two_le_cos (x := z.im)]
  have hScale : (9 / 10 : ℝ) ≤ discriminant23ThetaScale * Real.cos z.im :=
    (by norm_num : (9 / 10 : ℝ) ≤ (13 / 10) * (23 / 32)).trans
      (mul_le_mul discriminant23_thetaScale_interval.1 hCos (by norm_num)
        (by linarith only [discriminant23_thetaScale_interval.1]))
  have hHeat : ‖q‖ ≤ Real.exp (-(9 / 10 : ℝ) * Real.exp z.re) := by
    dsimp only [q]
    rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.exp_re]
    exact Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hScale (Real.exp_nonneg z.re)])
  have hUpper : ‖q‖ ≤ 5 / 6 := by
    refine hHeat.trans ((Real.exp_le_exp.mpr (show -(9 / 10 : ℝ) * Real.exp z.re ≤ -(9 / 40) by
      linarith only [Real.add_one_le_exp z.re, hx])).trans ?_)
    rw [Real.exp_neg, ← one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (49 / 40 : ℝ))
      (by linarith only [Real.add_one_le_exp (9 / 40 : ℝ)] : (49 / 40 : ℝ) ≤ Real.exp (9 / 40))
    exact h.trans (by norm_num)
  have hGeomRat : ∑ n ∈ Finset.range 32, (2 : ℚ) * (5 / 6 : ℚ) ^ n ≤ 12 := by decide +kernel
  have hGeom : ∑ n ∈ Finset.range 32, (2 : ℝ) * (5 / 6 : ℝ) ^ n ≤ 12 := by
    have hReal : ((∑ n ∈ Finset.range 32, (2 : ℚ) * (5 / 6 : ℚ) ^ n : ℚ) : ℝ) ≤
        ((12 : ℚ) : ℝ) := Rat.cast_le.mpr hGeomRat
    push_cast at hReal
    exact hReal
  have hScaled : Real.exp z.re * ‖q‖ ≤ 5 / 12 := by
    let x := (9 / 10 : ℝ) * Real.exp z.re
    have hlin : x ≤ Real.exp (x - 1) := by linarith only [Real.add_one_le_exp (x - 1)]
    have h := mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg (-x))
    rw [← Real.exp_add, show x - 1 + -x = -1 by ring] at h
    have hNeg : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
      rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.exp_one_gt_d9])
    have hQ := mul_le_mul_of_nonneg_left hHeat (Real.exp_nonneg z.re)
    unfold x at h
    rw [show -((9 / 10 : ℝ) * Real.exp z.re) = -(9 / 10 : ℝ) * Real.exp z.re by ring] at h
    nlinarith only [hQ, h, hNeg]
  have h := mul_le_mul_of_nonneg_left
    (discriminant23_panel_density_norm_le_of_geometric_bound hUpper hGeom) (Real.exp_nonneg z.re)
  change Real.exp z.re * ‖discriminant23PanelDensity z‖ ≤ Real.exp z.re * (12 * ‖q‖) at h
  calc
    _ ≤ Real.exp z.re * (12 * ‖q‖) := h
    _ = 12 * (Real.exp z.re * ‖q‖) := by ring
    _ ≤ 5 := by linarith only [hScaled]

private theorem panel_bounds_to_nineteen_halves {w z : ℂ} {c : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 19 / 2)
    (hc : c ∈ Icc (0 : ℝ) 3) (hz : z ∈ sphere (c : ℂ) (3 / 4 : ℝ)) :
    ‖discriminant23PanelValue w z‖ ≤ 30000 ∧ ‖discriminant23PanelSlope w z‖ ≤ 112500 := by
  obtain ⟨hx, hy⟩ := panel_xy hc.1 hz
  have hn : ‖z‖ ≤ 15 / 4 := by
    have hd := mem_sphere.mp hz
    rw [dist_eq_norm] at hd
    have h := norm_add_le (z - (c : ℂ)) (c : ℂ)
    rw [sub_add_cancel, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1] at h
    linarith only [h, hc.2]
  have hExp : Real.exp ((1 + (19 / 2 : ℝ)) * (3 / 4)) ≤ 3000 := by
    refine (Real.exp_le_exp.mpr (by norm_num : (1 + (19 / 2 : ℝ)) * (3 / 4) ≤ 8)).trans ?_
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _)
      (by linarith only [Real.exp_one_lt_d9] : Real.exp 1 ≤ 68 / 25) 8).trans (by norm_num)
  have hTerm (v : ℂ) (hL : 0 ≤ v.re) (hH : v.re ≤ 1) (hT : |v.im| ≤ 19 / 2) :
      ‖Complex.exp (v * z) * discriminant23PanelDensity z‖ ≤ 15000 := by
    rw [norm_mul]
    calc
      _ ≤ (Real.exp z.re * Real.exp ((1 + (19 / 2 : ℝ)) * (3 / 4))) *
          ‖discriminant23PanelDensity z‖ :=
        mul_le_mul_of_nonneg_right (exp_weight_on_panel hL hH hT hx hy) (norm_nonneg _)
      _ = (Real.exp z.re * ‖discriminant23PanelDensity z‖) *
          Real.exp ((1 + (19 / 2 : ℝ)) * (3 / 4)) := by ring
      _ ≤ (5 : ℝ) * 3000 :=
        mul_le_mul (panel_density_bound_three_quarters hx hy) hExp (Real.exp_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hw := hTerm w hlo hhi ht
  have hv := hTerm (1 - w)
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using ht)
  constructor
  · rw [discriminant23PanelValue, add_mul]
    exact (norm_add_le _ _).trans (by linarith only [hw, hv])
  · rw [discriminant23PanelSlope, mul_assoc, sub_mul, norm_mul]
    have hsub := (norm_sub_le _ _).trans (add_le_add hw hv)
    exact (mul_le_mul hn hsub (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem discriminant23_character_quadrature_bounds_to_nineteen_halves {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 19 / 2) :
    ‖discriminant23CharacterComplexModel w -
        ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ 23 / 10 ^ 8 ∧
    ‖deriv discriminant23CharacterComplexModel w -
        ninePointComposite (fun u ↦ discriminant23PanelSlope w u) 0 (3 / 64) 32‖ ≤ 85 / 10 ^ 8 := by
  have hAny {F : ℂ → ℂ} {M : ℝ} (hF : Differentiable ℂ F)
      (hB : ∀ c ∈ Icc (0 : ℝ) 3, ∀ z ∈ sphere (c : ℂ) (3 / 4 : ℝ), ‖F z‖ ≤ M) :
      ‖(∫ u in (0 : ℝ)..3, F (u : ℂ)) -
        ninePointComposite (fun u ↦ F u) 0 (3 / 64) 32‖ ≤
        3 * (1 + 41142 / 28350) * (M * (1 / 16) ^ (10 : ℕ) / (1 - 1 / 16)) := by
    have h := ninePointComposite_error_le (F := F) (a := 0) (h := 3 / 64)
      (R := (3 / 4 : ℝ≥0)) (M := M) 32 (by norm_num) (by norm_num) hF (by
        intro c hc z hz
        exact hB c (by convert hc using 1; norm_num) z hz)
    norm_num at h ⊢
    exact h
  have hModel : discriminant23CharacterComplexModel w =
      ∫ u in (0 : ℝ)..3, discriminant23PanelValue w (u : ℂ) := by
    simp_rw [discriminant23_panelValue_eq_integrand]
    rfl
  rw [hModel, discriminant23_characterComplexModel_deriv]
  exact ⟨(hAny (by unfold discriminant23PanelValue discriminant23PanelDensity; fun_prop)
    (fun _ hc _ hz ↦ (panel_bounds_to_nineteen_halves hlo hhi ht hc hz).1)).trans (by norm_num),
    (hAny (by unfold discriminant23PanelSlope discriminant23PanelDensity; fun_prop)
    (fun _ hc _ hz ↦ (panel_bounds_to_nineteen_halves hlo hhi ht hc hz).2)).trans (by norm_num)⟩

#print axioms discriminant23_character_quadrature_bounds_to_nineteen_halves

#print axioms discriminant23_panel_value_bound_at_height
#print axioms discriminant23_value_quadrature_bound_to_six
#print axioms discriminant23_character_quadrature_bounds_to_eight

end

end FieldTarget
