import ComplexNewtonCotes
import DedekindDiscriminant23CharacterComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace FieldTarget

open Complex MeasureTheory Metric Set
open scoped BigOperators Interval NNReal

noncomputable section

/-- The degree-32 theta polynomial at a complex logarithmic integration input. -/
def discriminant23PanelDensity (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 33, (discriminant23CharacterCoefficient n : ℂ) *
    Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z) ^ n

def discriminant23PanelValue (w z : ℂ) : ℂ :=
  (Complex.exp (w * z) + Complex.exp ((1 - w) * z)) * discriminant23PanelDensity z

def discriminant23PanelSlope (w z : ℂ) : ℂ :=
  z * (Complex.exp (w * z) - Complex.exp ((1 - w) * z)) * discriminant23PanelDensity z

theorem discriminant23_panelValue_eq_integrand (w : ℂ) (u : ℝ) :
    discriminant23PanelValue w u = discriminant23CharacterComplexIntegrand w u := by
  unfold discriminant23PanelValue discriminant23PanelDensity discriminant23CharacterComplexIntegrand
  change _ * (∑ n ∈ Finset.range 33, (discriminant23CharacterCoefficient n : ℂ) *
    Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp (u : ℂ)) ^ n) =
      _ * (discriminant23CharacterPolynomial (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℂ)
  congr 1
  symm
  unfold discriminant23CharacterPolynomial
  change Complex.ofRealHom (∑ n ∈ Finset.range 33, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  change ((↑(discriminant23CharacterCoefficient n) *
    Real.exp (-discriminant23ThetaScale * Real.exp u) ^ n : ℝ) : ℂ) = _
  push_cast
  rfl

private theorem panelValue_hasDerivAt (w z : ℂ) :
    HasDerivAt (fun v ↦ discriminant23PanelValue v z) (discriminant23PanelSlope w z) w := by
  have hw : HasDerivAt (fun v : ℂ ↦ v * z) z w := by
    simpa using (hasDerivAt_id w).mul_const z
  have hv : HasDerivAt (fun v : ℂ ↦ (1 - v) * z) (-z) w := by
    simpa using ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).mul_const z
  unfold discriminant23PanelValue discriminant23PanelSlope
  convert (hw.cexp.add hv.cexp).mul_const (discriminant23PanelDensity z) using 1
  ring

/-- The first derivative is obtained by integrating the same theta density against
the derivative of the reflected exponential pair. -/
theorem discriminant23_characterComplexModel_deriv (w : ℂ) :
    deriv discriminant23CharacterComplexModel w =
      ∫ u in (0 : ℝ)..3, discriminant23PanelSlope w (u : ℂ) := by
  have hmodel : discriminant23CharacterComplexModel =
      fun v ↦ ∫ u in (0 : ℝ)..3, discriminant23PanelValue v (u : ℂ) := by
    funext v
    simp_rw [discriminant23_panelValue_eq_integrand]
    rfl
  rw [hmodel]
  let S : Set (ℂ × ℝ) := closedBall w 1 ×ˢ [[(0 : ℝ), 3]]
  have hS : IsCompact S := (isCompact_closedBall _ _).prod isCompact_uIcc
  have hSlope : Continuous (fun p : ℂ × ℝ ↦ discriminant23PanelSlope p.1 (p.2 : ℂ)) := by
    unfold discriminant23PanelSlope discriminant23PanelDensity
    fun_prop
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hSlope.continuousOn
  have hInt (v : ℂ) : IntervalIntegrable (fun u : ℝ ↦ discriminant23PanelValue v u) volume 0 3 := by
    apply Continuous.intervalIntegrable
    unfold discriminant23PanelValue discriminant23PanelDensity
    fun_prop
  have hSlopeInt : IntervalIntegrable (fun u : ℝ ↦ discriminant23PanelSlope w u) volume 0 3 :=
    (hSlope.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hbd (u : ℝ) (hu : u ∈ Ι (0 : ℝ) 3) (v : ℂ) (hv : v ∈ ball w 1) :
      ‖discriminant23PanelSlope v u‖ ≤ B :=
    hB (v, u) ⟨ball_subset_closedBall hv, uIoc_subset_uIcc hu⟩
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v u ↦ discriminant23PanelValue v (u : ℂ))
    (F' := fun v u ↦ discriminant23PanelSlope v (u : ℂ))
    (bound := fun _ ↦ B)
    (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun v ↦ (hInt v).aestronglyMeasurable_restrict_uIoc)
    (hInt w) hSlopeInt.aestronglyMeasurable_restrict_uIoc
    (Filter.Eventually.of_forall hbd) intervalIntegrable_const
    (Filter.Eventually.of_forall fun u _ v _ ↦ panelValue_hasDerivAt v (u : ℂ))).2.deriv

private theorem panel_circle_coordinates {c : ℝ} {z : ℂ} (hc : c ∈ Icc (0 : ℝ) 3)
    (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) :
    -(1 / 4) ≤ z.re ∧ |z.im| ≤ 1 / 4 ∧ ‖z‖ ≤ 13 / 4 := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hr := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_eq hd
  have hi := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  have hn := norm_add_le (z - (c : ℂ)) (c : ℂ)
  rw [sub_add_cancel, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1] at hn
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  exact ⟨by linarith only [(abs_le.mp hr).1, hc.1], hi, by linarith only [hn, hc.2]⟩

private theorem exp_neg_one_le : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h])

private theorem exp_neg_fifteen_sixteenths_le : Real.exp (-(15 / 16 : ℝ)) ≤ 2 / 5 := by
  have h := Real.sum_le_exp_of_nonneg (x := (15 / 16 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← one_div, show (2 / 5 : ℝ) = 1 / (5 / 2) by norm_num]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h])

private theorem exp_thirteen_eighths_le : Real.exp (13 / 8 : ℝ) ≤ 6 := by
  have h := Real.exp_bound' (x := (13 / 16 : ℝ)) (n := 4) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h' : Real.exp (13 / 16 : ℝ) ≤ 12 / 5 := by linarith only [h]
  rw [show (13 / 8 : ℝ) = 13 / 16 + 13 / 16 by norm_num, Real.exp_add, ← pow_two]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) h' 2).trans (by norm_num)

private theorem panel_heat_norm_le {z : ℂ} (hz : |z.im| ≤ 1 / 4) :
    ‖Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)‖ ≤
      Real.exp (-(5 / 4) * Real.exp z.re) := by
  have hcos : (31 / 32 : ℝ) ≤ Real.cos z.im := by
    have hsq : z.im ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [← sq_abs z.im]
      exact pow_le_pow_left₀ (abs_nonneg _) hz 2
    have h := Real.one_sub_sq_div_two_le_cos (x := z.im)
    linarith only [hsq, h]
  have hscale : (5 / 4 : ℝ) ≤ discriminant23ThetaScale * Real.cos z.im := by
    calc
      _ ≤ (13 / 10 : ℝ) * (31 / 32) := by norm_num
      _ ≤ _ := mul_le_mul discriminant23_thetaScale_interval.1 hcos (by norm_num)
        (by linarith only [discriminant23_thetaScale_interval.1])
  rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.exp_re]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hscale (Real.exp_nonneg z.re)
  linarith only [h, mul_assoc discriminant23ThetaScale (Real.exp z.re) (Real.cos z.im),
    mul_comm (Real.exp z.re) (Real.cos z.im)]

private theorem panel_heat_bounds {z : ℂ} (hx : -(1 / 4) ≤ z.re) (hy : |z.im| ≤ 1 / 4) :
    ‖Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)‖ ≤ 2 / 5 ∧
      Real.exp z.re * ‖Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)‖ ≤ 3 / 10 := by
  have hheat := panel_heat_norm_le hy
  constructor
  · refine hheat.trans ((Real.exp_le_exp.mpr ?_).trans exp_neg_fifteen_sixteenths_le)
    linarith only [Real.add_one_le_exp z.re, hx]
  · have hl : (5 / 4 : ℝ) * Real.exp z.re ≤
        Real.exp ((5 / 4) * Real.exp z.re - 1) := by
      linarith only [Real.add_one_le_exp ((5 / 4 : ℝ) * Real.exp z.re - 1)]
    have hw := mul_le_mul_of_nonneg_right hl (Real.exp_nonneg (-(5 / 4) * Real.exp z.re))
    rw [← Real.exp_add, show (5 / 4 : ℝ) * Real.exp z.re - 1 +
      -(5 / 4) * Real.exp z.re = -1 by ring] at hw
    have hb := mul_le_mul_of_nonneg_left hheat (Real.exp_nonneg z.re)
    linarith only [hw, hb, exp_neg_one_le]

/-- Every coefficient of the retained theta polynomial has absolute value at most two. -/
theorem discriminant23_characterCoefficient_abs_le :
    ∀ n : Fin 33, |discriminant23CharacterCoefficient n| ≤ (2 : ℤ) := by
  decide +kernel

private theorem panel_density_norm_le {z : ℂ}
    (hq : ‖Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)‖ ≤ 2 / 5) :
    ‖discriminant23PanelDensity z‖ ≤
      5 * ‖Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)‖ := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  change ‖∑ n ∈ Finset.range 33, (discriminant23CharacterCoefficient n : ℂ) * q ^ n‖ ≤ 5 * ‖q‖
  rw [Finset.sum_range_succ', show discriminant23CharacterCoefficient 0 = 0 by decide +kernel]
  simp only [Int.cast_zero, zero_mul, add_zero]
  refine (norm_sum_le _ _).trans ?_
  have hs : ∑ n ∈ Finset.range 32, (2 : ℚ) * (2 / 5 : ℚ) ^ n ≤ 5 := by decide +kernel
  have hs' : ∑ n ∈ Finset.range 32, (2 : ℝ) * (2 / 5 : ℝ) ^ n ≤ 5 := by
    have hreal : ((∑ n ∈ Finset.range 32, (2 : ℚ) * (2 / 5 : ℚ) ^ n : ℚ) : ℝ) ≤
        ((5 : ℚ) : ℝ) := Rat.cast_le.mpr hs
    push_cast at hreal
    exact hreal
  calc
    _ ≤ ∑ n ∈ Finset.range 32, 2 * (2 / 5 : ℝ) ^ n * ‖q‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hk : n + 1 < 33 := by simpa using Nat.succ_lt_succ (Finset.mem_range.mp hn)
      have hc : ‖(discriminant23CharacterCoefficient (n + 1) : ℂ)‖ ≤ (2 : ℝ) := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast discriminant23_characterCoefficient_abs_le ⟨n + 1, hk⟩
      rw [norm_mul, norm_pow, pow_succ, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg _) hq n) (by positivity) (by norm_num))
        (norm_nonneg _)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)

private theorem panel_weighted_term_bound {w z : ℂ} (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) (hx : -(1 / 4) ≤ z.re) (hy : |z.im| ≤ 1 / 4) :
    ‖Complex.exp (w * z) * discriminant23PanelDensity z‖ ≤ 9 := by
  have hRe : w.re * z.re ≤ z.re + 1 / 4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hw₁) (show 0 ≤ z.re + 1 / 4 by linarith only [hx]), hw₀]
  have hIm : -(w.im * z.im) ≤ 11 / 8 := by
    calc
      _ ≤ |w.im * z.im| := neg_le_abs _
      _ = |w.im| * |z.im| := abs_mul _ _
      _ ≤ (11 / 2 : ℝ) * (1 / 4) :=
        mul_le_mul ht hy (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hweight : ‖Complex.exp (w * z)‖ ≤ 6 * Real.exp z.re := by
    rw [Complex.norm_exp, Complex.mul_re]
    calc
      _ ≤ Real.exp (z.re + 13 / 8) := Real.exp_le_exp.mpr (by linarith only [hRe, hIm])
      _ ≤ _ := by
        rw [Real.exp_add, mul_comm 6]
        exact mul_le_mul_of_nonneg_left exp_thirteen_eighths_le (Real.exp_nonneg _)
  obtain ⟨hq, hq'⟩ := panel_heat_bounds hx hy
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  rw [norm_mul]
  calc
    _ ≤ (6 * Real.exp z.re) * (5 * ‖q‖) :=
      mul_le_mul hweight (panel_density_norm_le hq) (norm_nonneg _) (by positivity)
    _ = 30 * (Real.exp z.re * ‖q‖) := by ring
    _ ≤ _ := by linarith only [hq']

/-- Uniform bounds on all of the logarithmic integration circles, for the value
and derivative together on the closed strip through height 11/2. -/
theorem discriminant23_panel_circle_bounds {w : ℂ} (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 3)
    {z : ℂ} (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) :
    ‖discriminant23PanelValue w z‖ ≤ 60 ∧ ‖discriminant23PanelSlope w z‖ ≤ 60 := by
  obtain ⟨hx, hy, hn⟩ := panel_circle_coordinates hc hz
  have hw := panel_weighted_term_bound hw₀ hw₁ ht hx hy
  have hv := panel_weighted_term_bound (w := 1 - w)
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hw₁])
    (by rw [Complex.sub_re, Complex.one_re]; linarith only [hw₀])
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using ht) hx hy
  constructor
  · rw [discriminant23PanelValue, add_mul]
    exact (norm_add_le _ _).trans (by linarith only [hw, hv])
  · rw [discriminant23PanelSlope, mul_assoc, sub_mul, norm_mul]
    have hsub := (norm_sub_le _ _).trans (add_le_add hw hv)
    exact (mul_le_mul hn hsub (norm_nonneg _) (by norm_num)).trans (by norm_num)

private theorem panel_quadrature_error {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hbound : ∀ c ∈ Icc (0 : ℝ) 3, ∀ z ∈ sphere (c : ℂ) (1 / 4 : ℝ), ‖F z‖ ≤ 60) :
    ‖(∫ u in (0 : ℝ)..3, F (u : ℂ)) -
      ninePointComposite (fun u ↦ F (u : ℂ)) 0 (3 / 64) 32‖ ≤ 3 / 100000 := by
  have h := ninePointComposite_error_le (F := F) (a := 0) (h := 3 / 64) (R := (1 / 4 : ℝ≥0))
    (M := 60) 32 (by norm_num) (by norm_num) hF (by
      intro c hc z hz
      exact hbound c (by convert hc using 1; norm_num) z hz)
  norm_num at h ⊢
  exact h.trans (by norm_num)

/-- A single 32-panel rule bounds both readings over the full stated rectangle. -/
theorem discriminant23_character_quadrature_bounds {w : ℂ}
    (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) (ht : |w.im| ≤ 11 / 2) :
    ‖discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ 3 / 100000 ∧
    ‖deriv discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelSlope w u) 0 (3 / 64) 32‖ ≤ 3 / 100000 := by
  have hvalue : Differentiable ℂ (discriminant23PanelValue w) := by
    unfold discriminant23PanelValue discriminant23PanelDensity
    fun_prop
  have hslope : Differentiable ℂ (discriminant23PanelSlope w) := by
    unfold discriminant23PanelSlope discriminant23PanelDensity
    fun_prop
  constructor
  · have h := panel_quadrature_error hvalue
      (fun _ hc _ hz ↦ (discriminant23_panel_circle_bounds hw₀ hw₁ ht hc hz).1)
    simpa only [discriminant23_panelValue_eq_integrand, discriminant23CharacterComplexModel] using h
  · rw [discriminant23_characterComplexModel_deriv]
    exact panel_quadrature_error hslope
      (fun _ hc _ hz ↦ (discriminant23_panel_circle_bounds hw₀ hw₁ ht hc hz).2)

#check @discriminant23_character_quadrature_bounds
#print axioms discriminant23_panelValue_eq_integrand
#print axioms discriminant23_characterComplexModel_deriv
#print axioms discriminant23_panel_circle_bounds
#print axioms discriminant23_characterCoefficient_abs_le
#print axioms discriminant23_character_quadrature_bounds

end

end FieldTarget

