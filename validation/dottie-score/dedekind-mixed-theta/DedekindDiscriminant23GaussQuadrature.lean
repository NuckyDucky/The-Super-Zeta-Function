import Gauss24PanelTable
import DedekindDiscriminant23AdaptiveParameters

/-! The value and slope use the same finite rational quadrature rule. -/

namespace FieldTarget

open MeasureTheory Metric Set Complex
open scoped Interval NNReal

noncomputable section

def discriminant23GaussIntegrand (slope : Bool) (w z : ℂ) : ℂ :=
  (if slope then z * (Complex.exp ((w - 1) * z) - Complex.exp (-w * z))
    else Complex.exp ((w - 1) * z) + Complex.exp (-w * z)) * discriminant23PhaseDensityUpTo 64 z

def discriminant23GaussReading (slope : Bool) (w : ℂ) : ℂ :=
  rationalCompositeRule gauss24Node gauss24Weight
    (fun u ↦ discriminant23GaussIntegrand slope w u) 0 (1 / 8) 16

private theorem d23GaussIntegrand_differentiable (slope : Bool) (w : ℂ) :
    Differentiable ℂ (discriminant23GaussIntegrand slope w) := by
  cases slope <;> unfold discriminant23GaussIntegrand discriminant23PhaseDensityUpTo
    discriminant23CharacterPolynomialUpTo <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

private theorem d23GaussIntegrand_norm_le (slope : Bool) {w z : ℂ} {c r : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hc : c ∈ Icc (0 : ℝ) 4) (hz : z ∈ sphere (c : ℂ) r) :
    ‖discriminant23GaussIntegrand slope w z‖ ≤ 1740 * Real.exp ((|w.im| + 1) * r) := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hy := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  have hx := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hy
  simp only [Complex.sub_re, Complex.ofReal_re] at hx
  have hLower : -r ≤ z.re := by
    linarith only [(abs_le.mp hx).1, hc.1]
  have hnorm : ‖z‖ ≤ 5 := by
    have h := norm_add_le (z - (c : ℂ)) (c : ℂ)
    rw [sub_add_cancel, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1] at h
    linarith only [h, hc.2, hr₁]
  have hExp (v : ℂ) (hl : -1 ≤ v.re) (hh : v.re ≤ 0) (hi : |v.im| ≤ |w.im|) :
      ‖Complex.exp (v * z)‖ ≤ Real.exp ((|w.im| + 1) * r) := by
    have hRe : v.re * z.re ≤ r := by
      have h := mul_le_mul_of_nonpos_left hLower hh
      linarith only [h, mul_le_mul_of_nonneg_right hl hr₀]
    have hIm : -(v.im * z.im) ≤ |w.im| * r := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul hi hy (abs_nonneg _) (abs_nonneg _)
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by rw [Complex.mul_re]; linarith only [hRe, hIm])
  have h₁ := hExp (w - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by simp only [Complex.sub_im, Complex.one_im, sub_zero, le_refl])
  have h₂ := hExp (-w) (by simp only [Complex.neg_re]; linarith only [hhi])
    (by simp only [Complex.neg_re]; linarith only [hlo])
    (by simp only [Complex.neg_im, abs_neg, le_refl])
  have hCount : discriminant23PhaseTermCount 64 = 174 := by decide +kernel
  have hDensity : ‖discriminant23PhaseDensityUpTo 64 z‖ ≤ 174 := by
    calc
      _ ≤ (discriminant23PhaseTermCount 64 : ℝ) :=
        discriminant23_phaseDensity_norm_le_of_abs_im_le_one _ (hy.trans hr₁)
      _ = _ := by rw [hCount]; norm_num
  cases slope
  · simp only [discriminant23GaussIntegrand, Bool.false_eq_true, ↓reduceIte, norm_mul]
    exact (mul_le_mul (norm_add_le _ _ |>.trans (add_le_add h₁ h₂)) hDensity
      (norm_nonneg _) (by positivity)).trans (by linarith only [Real.exp_nonneg ((|w.im| + 1) * r)])
  · simp only [discriminant23GaussIntegrand, ↓reduceIte, norm_mul]
    have hg := mul_le_mul hnorm (norm_sub_le _ _ |>.trans (add_le_add h₁ h₂))
      (norm_nonneg _) (by norm_num)
    exact (mul_le_mul hg hDensity (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem discriminant23_gaussIntegrand_real_eq (slope : Bool) (w : ℂ) (u : ℝ) :
    discriminant23GaussIntegrand slope w (u : ℂ) =
      (if slope then (u : ℂ) * (Complex.exp (w * u) - Complex.exp ((1 - w) * u))
        else Complex.exp (w * u) + Complex.exp ((1 - w) * u)) *
      (discriminant23CharacterPolynomialUpTo 64
        (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
  have h : discriminant23PhaseDensityUpTo 64 (u : ℂ) = Complex.exp (u : ℂ) *
      (discriminant23CharacterPolynomialUpTo 64
        (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
    simp only [discriminant23PhaseDensityUpTo, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, discriminant23_characterPolynomialUpTo_ofReal]
  have h₁ : Complex.exp ((w - 1) * (u : ℂ)) * Complex.exp (u : ℂ) = Complex.exp (w * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h₂ : Complex.exp (-w * (u : ℂ)) * Complex.exp (u : ℂ) = Complex.exp ((1 - w) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  cases slope <;> simp only [discriminant23GaussIntegrand, Bool.false_eq_true, ↓reduceIte, h] <;>
    rw [← h₁, ← h₂] <;> ring

def discriminant23GaussErrorBudget (T : ℝ) : ℝ :=
  1 / 10 ^ 23 + (20880 * Real.exp ((T + 1) * (3 / 4)) * (1 / 6) ^ (48 : ℕ) +
    6960 * Real.exp ((T + 1) / 4) / 10 ^ 30)

/-- A height-dependent error for the same rational rule, using separate Cauchy radii. -/
theorem discriminant23_gaussReading_error_of_height (slope : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23GaussReading slope w‖ < discriminant23GaussErrorBudget |w.im| := by
  let model := discriminant23CharacterModelUpTo 64 (Real.exp 4)
  let A := if slope then deriv model w else model w
  have hR : 1 ≤ Real.exp 4 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  have hmodel : ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
      A‖ ≤ discriminant23CharacterModelError 46 (Real.exp 4) := by
    cases slope
    · exact discriminant23_characterModelUpTo_error (N := 64) (by decide) (by decide) hR
        (by linarith only [hlo]) (by linarith only [hhi])
    · have h := discriminant23_characterModelUpTo_iteratedDeriv_error 1 (N := 64) (order := 46)
        (by decide) (by decide) hR hlo hhi
      simpa only [A, model, ↓reduceIte, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul] using h
  have hInt : A = ∫ x in (0 : ℝ)..4, discriminant23GaussIntegrand slope w (x : ℂ) := by
    cases slope
    · simp only [A, model, Bool.false_eq_true, ↓reduceIte,
        discriminant23_characterModelUpTo_eq_logIntegral, discriminant23_gaussIntegrand_real_eq]
    · simp only [A, model, ↓reduceIte, discriminant23_gaussIntegrand_real_eq,
        discriminant23_characterModelUpTo_deriv_eq_logIntegral 64 (by norm_num : (0 : ℝ) ≤ 4)]
  have hQuad := rationalCompositeRule_twoRadius_error_le gauss24Node gauss24Weight
    (F := discriminant23GaussIntegrand slope w) (a := 0) (h := 1 / 8)
    (R := (3 / 4 : ℝ≥0)) (r := (1 / 4 : ℝ≥0))
    (M := 1740 * Real.exp ((|w.im| + 1) * (3 / 4)))
    (mInner := 1740 * Real.exp ((|w.im| + 1) / 4)) (δ := 1 / 10 ^ 30) (W := 3) 48 16
    (by norm_num) (by norm_num) (by apply NNReal.coe_le_coe.mp; norm_num) (by norm_num)
    gauss24_node_abs_le gauss24_weight_abs_sum_le
    (fun _ hk ↦ gauss24_moment_error_tight hk) (d23GaussIntegrand_differentiable slope w)
    (fun c hc z hz ↦ d23GaussIntegrand_norm_le slope hlo hhi (by norm_num) (by norm_num)
      (by convert hc using 1; norm_num) (show z ∈ sphere (c : ℂ) (3 / 4 : ℝ) from hz))
    (fun c hc z hz ↦ by
      have h := d23GaussIntegrand_norm_le slope hlo hhi (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (by norm_num) (by convert hc using 1; norm_num)
        (show z ∈ sphere (c : ℂ) (1 / 4 : ℝ) from hz)
      simpa only [div_eq_mul_inv, one_mul] using h)
  have hq : ‖A - discriminant23GaussReading slope w‖ ≤
      20880 * Real.exp ((|w.im| + 1) * (3 / 4)) * (1 / 6) ^ (48 : ℕ) +
        6960 * Real.exp ((|w.im| + 1) / 4) / 10 ^ 30 := by
    rw [hInt, discriminant23GaussReading]
    norm_num at hQuad ⊢
    linarith only [hQuad]
  exact (norm_sub_le_norm_sub_add_norm_sub _ A _).trans_lt
    (add_lt_add_of_lt_of_le (hmodel.trans_lt discriminant23_modelError_at_64_4) hq)

private theorem exp_le_rational_power (n : ℕ) {x : ℝ} (hx : x ≤ n) :
    Real.exp x ≤ (11 / 4 : ℝ) ^ n := by
  calc
    _ ≤ Real.exp ((n : ℝ) * 1) := Real.exp_le_exp.mpr (by simpa only [mul_one] using hx)
    _ = Real.exp 1 ^ n := Real.exp_nat_mul 1 n
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith only [Real.exp_one_lt_d9]) _

theorem discriminant23_gaussReading_error_of_twentyEight (slope : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 28) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23GaussReading slope w‖ < 5 / 10 ^ 23 := by
  have hLarge := exp_le_rational_power 22
    (show (|w.im| + 1) * (3 / 4) ≤ (22 : ℝ) by linarith only [ht])
  have hSmall := exp_le_rational_power 8 (show (|w.im| + 1) / 4 ≤ (8 : ℝ) by linarith only [ht])
  refine (discriminant23_gaussReading_error_of_height slope hlo hhi).trans ?_
  unfold discriminant23GaussErrorBudget
  norm_num at hLarge hSmall ⊢
  linarith only [hLarge, hSmall]

theorem discriminant23_gaussReading_error (slope : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 20) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23GaussReading slope w‖ < 2 / 10 ^ 19 :=
  (discriminant23_gaussReading_error_of_twentyEight slope hlo hhi (ht.trans (by norm_num))).trans (by norm_num)

#print axioms discriminant23_gaussReading_error_of_height
#print axioms discriminant23_gaussReading_error_of_twentyEight
#print axioms discriminant23_gaussReading_error

end

end FieldTarget
