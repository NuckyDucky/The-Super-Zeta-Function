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

private theorem d23GaussIntegrand_norm_le (slope : Bool) {w z : ℂ} {c : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 20)
    (hc : c ∈ Icc (0 : ℝ) 4) (hz : z ∈ sphere (c : ℂ) (1 / 2 : ℝ)) :
    ‖discriminant23GaussIntegrand slope w z‖ ≤ 300000000 := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hy := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  have hx := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hy
  simp only [Complex.sub_re, Complex.ofReal_re] at hx
  have hLower : -(1 / 2 : ℝ) ≤ z.re := by
    linarith only [(abs_le.mp hx).1, hc.1]
  have hnorm : ‖z‖ ≤ 9 / 2 := by
    have h := norm_add_le (z - (c : ℂ)) (c : ℂ)
    rw [sub_add_cancel, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1] at h
    linarith only [h, hc.2]
  have hExp (v : ℂ) (hl : -1 ≤ v.re) (hh : v.re ≤ 0) (hi : |v.im| ≤ 20) :
      ‖Complex.exp (v * z)‖ ≤ 177147 := by
    have hRe : v.re * z.re ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonpos_left hLower hh
      linarith only [h, hl]
    have hIm : -(v.im * z.im) ≤ 10 := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact (mul_le_mul hi hy (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [Complex.norm_exp]
    calc
      _ ≤ Real.exp 11 := Real.exp_le_exp.mpr (by rw [Complex.mul_re]; linarith only [hRe, hIm])
      _ = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ 11 := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le _
      _ = _ := by norm_num
  have h₁ := hExp (w - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using ht)
  have h₂ := hExp (-w) (by simp only [Complex.neg_re]; linarith only [hhi])
    (by simp only [Complex.neg_re]; linarith only [hlo])
    (by simpa only [Complex.neg_im, abs_neg] using ht)
  have hCount : discriminant23PhaseTermCount 64 = 174 := by decide +kernel
  have hDensity : ‖discriminant23PhaseDensityUpTo 64 z‖ ≤ 174 := by
    calc
      _ ≤ (discriminant23PhaseTermCount 64 : ℝ) := discriminant23_phaseDensity_norm_le _ hy
      _ = _ := by rw [hCount]; norm_num
  cases slope
  · simp only [discriminant23GaussIntegrand, Bool.false_eq_true, ↓reduceIte, norm_mul]
    exact (mul_le_mul (norm_add_le _ _ |>.trans (add_le_add h₁ h₂)) hDensity
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  · simp only [discriminant23GaussIntegrand, ↓reduceIte, norm_mul]
    have hg := mul_le_mul hnorm (norm_sub_le _ _ |>.trans (add_le_add h₁ h₂))
      (norm_nonneg _) (by norm_num)
    exact (mul_le_mul hg hDensity (norm_nonneg _) (by norm_num)).trans (by norm_num)

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

theorem discriminant23_gaussReading_error (slope : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 20) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23GaussReading slope w‖ < 2 / 10 ^ 19 := by
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
  have hQuad := rationalCompositeRule_error_le gauss24Node gauss24Weight
    (F := discriminant23GaussIntegrand slope w) (a := 0) (h := 1 / 8) (R := (1 / 2 : ℝ≥0))
    (M := 300000000) (δ := 1 / 10 ^ 28) (W := 3) 48 16
    (by norm_num) (by norm_num) (by norm_num) gauss24_node_abs_le gauss24_weight_abs_sum_le
    (fun _ hk ↦ gauss24_moment_error hk) (d23GaussIntegrand_differentiable slope w)
    (fun c hc z hz ↦ d23GaussIntegrand_norm_le slope hlo hhi ht (by convert hc using 1; norm_num) hz)
  have hq : ‖A - discriminant23GaussReading slope w‖ ≤
      (16 : ℝ) * ((1 / 8) * 300000000 / (1 - 1 / 4) * ((2 + 3) * (1 / 4) ^ (48 : ℕ) + 1 / 10 ^ 28)) := by
    rw [hInt, discriminant23GaussReading]
    norm_num at hQuad ⊢
    exact hQuad
  refine (norm_sub_le_norm_sub_add_norm_sub _ A _).trans_lt
    ((add_le_add hmodel hq).trans_lt ?_)
  have he := discriminant23_modelError_at_64_4
  norm_num at he ⊢
  linarith only [he]

#print axioms discriminant23_gaussReading_error

end

end FieldTarget
