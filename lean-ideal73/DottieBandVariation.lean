import DottieSignedBlockVariation
import ArchivedDottieRangeIntegral

/-! Keep the terminal signed mass separate from the intermediate prefix
bound when applying Abel summation to one of the retained norm bands. -/

namespace QuarticModel

open Complex Finset
set_option autoImplicit false

theorem dottie_band_abel_bound (c f : ℕ → ℂ) (n : ℕ) (A M V : ℝ)
    (hprefix : ∀ k ≤ n, ‖∑ i ∈ range k, c i‖ ≤ A)
    (hterminal : ‖∑ i ∈ range (n+1), c i‖ ≤ M)
    (hstep : ∀ i < n, ‖f (i+1)-f i‖ ≤ V) :
    ‖∑ i ∈ range (n+1), f i*c i‖ ≤ ‖f n‖*M + (n : ℝ)*V*A := by
  have hparts := Finset.sum_range_by_parts f c (n+1)
  simp only [smul_eq_mul,Nat.add_sub_cancel] at hparts
  rw [hparts]
  calc
    _ ≤ ‖f n * ∑ i ∈ range (n+1), c i‖ +
        ‖∑ i ∈ range n, (f (i+1)-f i) * ∑ j ∈ range (i+1), c j‖ := norm_sub_le _ _
    _ ≤ ‖f n‖*M + ∑ _i ∈ range n, V*A := by
      refine add_le_add ?_ ((norm_sum_le _ _).trans ?_)
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left hterminal (norm_nonneg _)
      · refine sum_le_sum fun i hi => ?_
        rw [Complex.norm_mul]
        exact mul_le_mul (hstep i (mem_range.mp hi))
          (hprefix (i+1) (mem_range.mp hi)) (norm_nonneg _) (by
            exact (norm_nonneg _).trans (hstep i (mem_range.mp hi)))
    _ = _ := by simp [mul_assoc]

theorem dottie_band_exp_step {z : ℂ} (hz : ‖z‖ ≤ 1/1000) :
    ‖Complex.exp z - 1‖ ≤ (1001/1000)*‖z‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le (hz.trans (by norm_num))
  calc
    _ = ‖Complex.exp z - 1 - z + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Complex.exp z - 1 - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖^2 + ‖z‖ := add_le_add h le_rfl
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)]

/-- One unit step of the original contour weight, controlled from the
left endpoint of the band. -/
theorem dottie_band_cpow_step {B a x : ℝ} (hB : 0 < B) (ha : 0 < a) (hax : a ≤ x)
    {q : ℂ} (hq : 0 ≤ q.re) (hsmall : ‖q‖/a ≤ 1/1000) :
    ‖((B/(x+1) : ℝ) : ℂ)^q - ((B/x : ℝ) : ℂ)^q‖ ≤
      (B/a)^q.re * ((1001/1000)*(‖q‖/a)) := by
  have hx : 0 < x := ha.trans_le hax
  have hx₁ : 0 < x+1 := by positivity
  have hv : 0 < (x+1)/x := div_pos hx₁ hx
  have hl₀ : 0 ≤ Real.log ((x+1)/x) := Real.log_nonneg (by
    rw [le_div_iff₀ hx]
    linarith)
  have hl : Real.log ((x+1)/x) ≤ 1/a := calc
    _ ≤ (x+1)/x-1 := Real.log_le_sub_one_of_pos hv
    _ = 1/x := by field_simp; ring
    _ ≤ _ := one_div_le_one_div_of_le ha hax
  let z : ℂ := -(Real.log ((x+1)/x) : ℂ)*q
  have hz : ‖z‖ ≤ ‖q‖/a := by
    rw [show z = -(Real.log ((x+1)/x) : ℂ)*q from rfl, Complex.norm_mul,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl₀]
    simpa only [one_div, div_eq_inv_mul ‖q‖ a] using
      mul_le_mul_of_nonneg_right hl (norm_nonneg q)
  have hb := div_pos hB hx
  have hb₁ := div_pos hB hx₁
  have hlog : Real.log (B/(x+1)) = Real.log (B/x)-Real.log ((x+1)/x) := by
    have he : B/(x+1) = (B/x)/((x+1)/x) := by field_simp
    rw [he, Real.log_div hb.ne' hv.ne']
  have hweight : ((B/(x+1) : ℝ) : ℂ)^q = ((B/x : ℝ) : ℂ)^q * Complex.exp z := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb₁.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
      ← Complex.ofReal_log hb₁.le, ← Complex.ofReal_log hb.le, hlog, Complex.ofReal_sub]
    rw [show ((Real.log (B/x) : ℂ) - (Real.log ((x+1)/x) : ℂ))*q =
      (Real.log (B/x) : ℂ)*q+z by dsimp [z]; ring, Complex.exp_add]
  rw [hweight, ← mul_sub_one, Complex.norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb]
  refine mul_le_mul ?_ ((dottie_band_exp_step (hz.trans hsmall)).trans ?_) (norm_nonneg _) ?_
  · exact Real.rpow_le_rpow hb.le (div_le_div_of_nonneg_left hB.le ha hax) hq
  · exact mul_le_mul_of_nonneg_left hz (by norm_num)
  · positivity

/-- In the exact contour polynomial, only signed integer prefix sums and
the signed terminal sum of the original coefficients enter. -/
theorem dottie_band_polynomial_bound {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {q : ℂ} (hq : 0 ≤ q.re) (hsmall : ‖q‖/(a : ℝ) ≤ 1/1000) (A M : ℝ)
    (hprefix : ∀ k ≤ b-a, ‖∑ i ∈ range k, (archivedLatticeCoeff (a+i) : ℂ)‖ ≤ A)
    (hterminal : ‖∑ i ∈ range (b-a+1), (archivedLatticeCoeff (a+i) : ℂ)‖ ≤ M) :
    ‖dottieRangePolynomial (Icc a b) q‖ ≤
      (archivedThetaScale/(a : ℝ))^q.re *
        (M+A*((1001/1000)*(‖q‖/(a : ℝ)))*(b-a : ℕ)) := by
  let B := archivedThetaScale
  let f (i : ℕ) := ((B/((a+i : ℕ) : ℝ) : ℝ) : ℂ)^q
  let c (i : ℕ) := (archivedLatticeCoeff (a+i) : ℂ)
  let R := (B/(a : ℝ))^q.re
  let V := (1001/1000)*(‖q‖/(a : ℝ))
  have hAr : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hstep (i : ℕ) (_ : i < b-a) : ‖f (i+1)-f i‖ ≤ R*V := by
    have hax : (a : ℝ) ≤ ((a+i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right a i
    simpa only [f,R,V,B,Nat.cast_add,Nat.cast_one,← add_assoc] using
      (dottie_band_cpow_step archivedThetaScale_pos hAr hax hq hsmall)
  have hf : ‖f (b-a)‖ ≤ R := by
    let x := ((a+(b-a) : ℕ) : ℝ)
    have hax : (a : ℝ) ≤ x := by
      dsimp [x]
      exact_mod_cast Nat.le_add_right a (b-a)
    have hB := archivedThetaScale_pos
    have hBx : 0 < B/x := div_pos hB (hAr.trans_le hax)
    change ‖((B/x : ℝ) : ℂ)^q‖ ≤ R
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hBx]
    exact Real.rpow_le_rpow hBx.le (div_le_div_of_nonneg_left hB.le hAr hax) hq
  have hM := (norm_nonneg _).trans hterminal
  have he : dottieRangePolynomial (Icc a b) q = ∑ i ∈ range (b-a+1), f i*c i := by
    rw [dottieRangePolynomial, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
      show b+1-a = b-a+1 by omega]
    exact sum_congr rfl (fun i _ => by simp only [f,c,B,mul_comm])
  rw [he]
  calc
    _ ≤ ‖f (b-a)‖*M + ((b-a : ℕ) : ℝ)*(R*V)*A :=
      dottie_band_abel_bound c f (b-a) A M (R*V) hprefix hterminal hstep
    _ ≤ R*M + ((b-a : ℕ) : ℝ)*(R*V)*A :=
      add_le_add (mul_le_mul_of_nonneg_right hf hM) le_rfl
    _ = _ := by dsimp [R,V,B]; ring

/-- Relative phase-length bounds for the three merged bands on the core
contour. Each allows the same one-third budget in Abel summation. -/
theorem dottie_retained_band_phase_lengths :
    let m (a b : ℝ) := (1001/1000)*4527000000000*(b-a)/a
    m 1854467118035498894 1854467118035634061 ≤ 1/3 ∧
    m 3708934236071001884 3708934236071268123 ≤ 1/3 ∧
    m 7417868472142007863 7417868472142536246 ≤ 1/3 := by
  norm_num

#print axioms dottie_band_abel_bound
#print axioms dottie_band_exp_step
#print axioms dottie_band_cpow_step
#print axioms dottie_band_polynomial_bound
#print axioms dottie_retained_band_phase_lengths

end QuarticModel
