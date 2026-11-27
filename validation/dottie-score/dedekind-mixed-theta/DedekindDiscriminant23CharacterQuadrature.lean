import DedekindDiscriminant23CharacterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

namespace FieldTarget

open Set Finset
open scoped Interval

noncomputable section

private def modeExponent (a t u : ℝ) : ℂ :=
  (1 / 2 + (t : ℂ) * Complex.I) * (u : ℂ) - (a * Real.exp u : ℝ)

private def modeSlope (a t u : ℝ) : ℂ :=
  (1 / 2 + (t : ℂ) * Complex.I) - (a * Real.exp u : ℝ)

private def modeValue (a t u : ℝ) : ℂ := Complex.exp (modeExponent a t u)

private def modeFirst (a t u : ℝ) : ℝ := (modeValue a t u * modeSlope a t u).re

private def modeSecond (a t u : ℝ) : ℝ :=
  (modeValue a t u * (modeSlope a t u ^ 2 - (a * Real.exp u : ℝ))).re

private theorem exp_cast_deriv (a u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ ((a * Real.exp v : ℝ) : ℂ))
      ((a * Real.exp u : ℝ) : ℂ) u :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u ((Real.hasDerivAt_exp u).const_mul a)

private theorem modeSlope_deriv (a t u : ℝ) :
    HasDerivAt (modeSlope a t) (-((a * Real.exp u : ℝ) : ℂ)) u := by
  unfold modeSlope
  simpa only [zero_sub, Pi.sub_def] using
    (hasDerivAt_const u (1 / 2 + (t : ℂ) * Complex.I)).sub (exp_cast_deriv a u)

private theorem modeValue_deriv (a t u : ℝ) :
    HasDerivAt (modeValue a t) (modeValue a t u * modeSlope a t u) u := by
  have hReal : HasDerivAt (fun v : ℝ ↦ (v : ℂ)) (1 : ℂ) u := by
    change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) u
    exact Complex.ofRealCLM.hasDerivAt
  have h := (hReal.const_mul (1 / 2 + (t : ℂ) * Complex.I)).sub (exp_cast_deriv a u)
  have h' : HasDerivAt (modeExponent a t) (modeSlope a t u) u := by
    unfold modeExponent modeSlope
    simpa only [Pi.sub_def, mul_one] using h
  exact h'.cexp

private theorem modeReal_deriv (a t u : ℝ) :
    HasDerivAt (fun v ↦ (modeValue a t v).re) (modeFirst a t u) u :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (modeValue_deriv a t u)

private theorem modeFirst_deriv (a t u : ℝ) :
    HasDerivAt (modeFirst a t) (modeSecond a t u) u := by
  have h := (modeValue_deriv a t u).mul (modeSlope_deriv a t u)
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  convert hRe using 1 <;> try rfl
  unfold modeSecond
  rw [Complex.reCLM_apply]
  congr 1
  ring

private theorem two_mul_le_exp {x : ℝ} (hx : 0 ≤ x) : 2 * x ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg (x - 1)]

private theorem decay_polynomial_le {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3 + x ^ 2 + 31 * x) * Real.exp (-x) ≤ 21 := by
  have h₂a := two_mul_le_exp (div_nonneg hx (by norm_num : (0 : ℝ) ≤ 2))
  have h₂b : x ≤ Real.exp (x / 2) := by linarith only [h₂a]
  have h₂c := pow_le_pow_left₀ hx h₂b 2
  have h₂ : x ^ 2 ≤ Real.exp x := by
    rw [pow_two (Real.exp (x / 2)), ← Real.exp_add, show x / 2 + x / 2 = x by ring] at h₂c
    exact h₂c
  have h₃a := two_mul_le_exp (div_nonneg hx (by norm_num : (0 : ℝ) ≤ 3))
  have h₃b := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (x / 3)) h₃a 3
  have h₃ : x ^ 3 ≤ 4 * Real.exp x := by
    rw [← Real.exp_nat_mul, show (3 : ℕ) * (x / 3) = x by norm_num; ring] at h₃b
    nlinarith only [h₃b, Real.exp_nonneg x]
  have hProd : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hq := Real.exp_nonneg (-x)
  have h1 := mul_le_mul_of_nonneg_right (two_mul_le_exp hx) hq
  have h2 := mul_le_mul_of_nonneg_right h₂ hq
  have h3 := mul_le_mul_of_nonneg_right h₃ hq
  rw [hProd] at h1 h2
  rw [mul_assoc, hProd, mul_one] at h3
  nlinarith only [h1, h2, h3]

private theorem modeSecond_abs_le {a t u : ℝ} (ha : 0 < a)
    (ht : |t| ≤ 11 / 2) (hu : 0 ≤ u) : |modeSecond a t u| ≤ 21 / a := by
  let v := a * Real.exp u
  have hv : 0 ≤ v := mul_nonneg ha.le (Real.exp_nonneg _)
  have htsq : t ^ 2 ≤ (11 / 2 : ℝ) ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hsq : ‖modeSlope a t u‖ ^ 2 = (1 / 2 - v) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [modeSlope, v, Complex.mul_re, Complex.mul_im, Complex.exp_re]
    ring
  have hSlope : ‖modeSlope a t u ^ 2 - (v : ℂ)‖ ≤ v ^ 2 + v + 31 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv, hsq]
    nlinarith only [htsq, hv]
  have hRe : (modeExponent a t u).re = u / 2 - v := by
    simp [modeExponent, v, Complex.mul_re, Complex.mul_im, Complex.exp_re]
    ring
  have hE : ‖modeValue a t u‖ ≤ Real.exp u * Real.exp (-v) := by
    rw [modeValue, Complex.norm_exp, hRe, sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _)
  unfold modeSecond
  change |(modeValue a t u * (modeSlope a t u ^ 2 - (v : ℂ))).re| ≤ _
  calc
    _ ≤ ‖modeValue a t u * (modeSlope a t u ^ 2 - (v : ℂ))‖ := Complex.abs_re_le_norm _
    _ ≤ (Real.exp u * Real.exp (-v)) * (v ^ 2 + v + 31) := by
      rw [norm_mul]
      exact mul_le_mul hE hSlope (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = ((v ^ 3 + v ^ 2 + 31 * v) * Real.exp (-v)) / a := by
      apply (eq_div_iff ha.ne').2
      dsimp [v]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (decay_polynomial_le hv) ha.le

private theorem coefficientWeights_checked :
    (∑ n ∈ Ico 1 33, |(discriminant23CharacterCoefficient n : ℚ)| / (n : ℚ)) ≤ 6 := by
  decide +kernel

private theorem logPolynomial_eq_modes (t u : ℝ) :
    discriminant23CharacterLogPolynomial t u =
      ∑ n ∈ Ico 1 33, (2 * (discriminant23CharacterCoefficient n : ℝ)) *
        (modeValue (discriminant23ThetaScale * n) t u).re := by
  change 2 * Real.exp (u / 2) * Real.cos (t * u) *
    (∑ n ∈ range 33, (discriminant23CharacterCoefficient n : ℝ) *
      (Real.exp (-discriminant23ThetaScale * Real.exp u)) ^ n) = _
  rw [mul_sum]
  have hm (n : ℕ) :
      (modeValue (discriminant23ThetaScale * n) t u).re =
        Real.exp (u / 2) *
          (Real.exp (-discriminant23ThetaScale * Real.exp u) ^ n) * Real.cos (t * u) := by
    rw [modeValue, Complex.exp_re, ← Real.exp_nat_mul]
    have hh₁ : (modeExponent (discriminant23ThetaScale * n) t u).re =
        u / 2 + (n : ℝ) * (-discriminant23ThetaScale * Real.exp u) := by
      simp [modeExponent, Complex.mul_re, Complex.exp_re]
      ring
    have hh₂ : (modeExponent (discriminant23ThetaScale * n) t u).im = t * u := by
      simp [modeExponent, Complex.mul_im, Complex.mul_re]
    rw [hh₁, hh₂, Real.exp_add]
  rw [← sum_subset (s₁ := Ico 1 33) (s₂ := range 33)]
  · apply sum_congr rfl
    intro n _
    rw [hm n]
    ring
  · intro n hn
    exact mem_range.mpr (mem_Ico.mp hn).2
  · intro n hn hn'
    have h0 : n = 0 := by
      simp only [Finset.mem_range, Finset.mem_Ico] at hn hn'
      omega
    subst n
    norm_num [discriminant23CharacterCoefficient]

private theorem logPolynomial_second_eq (t : ℝ) :
    deriv (deriv (discriminant23CharacterLogPolynomial t)) =
      fun u ↦ ∑ n ∈ Ico 1 33, (2 * (discriminant23CharacterCoefficient n : ℝ)) *
        modeSecond (discriminant23ThetaScale * n) t u := by
  have h₀ := funext (logPolynomial_eq_modes t)
  rw [h₀]
  have h₁ : deriv (fun u ↦ ∑ n ∈ Ico 1 33,
        (2 * (discriminant23CharacterCoefficient n : ℝ)) *
        (modeValue (discriminant23ThetaScale * n) t u).re) =
        fun u ↦ ∑ n ∈ Ico 1 33, (2 * (discriminant23CharacterCoefficient n : ℝ)) *
          modeFirst (discriminant23ThetaScale * n) t u := by
    funext u
    rw [deriv_fun_sum]
    · apply sum_congr rfl
      intro n _
      exact ((modeReal_deriv _ _ _).const_mul _).deriv
    · intro n _
      exact ((modeReal_deriv _ _ _).const_mul _).differentiableAt
  rw [h₁]
  funext u
  rw [deriv_fun_sum]
  · apply sum_congr rfl
    intro n _
    exact ((modeFirst_deriv _ _ _).const_mul _).deriv
  · intro n _
    exact ((modeFirst_deriv _ _ _).const_mul _).differentiableAt

private theorem logPolynomial_second_abs_le {t u : ℝ} (ht : |t| ≤ 11 / 2) (hu : 0 ≤ u) :
    |deriv (deriv (discriminant23CharacterLogPolynomial t)) u| ≤ 252 := by
  rw [logPolynomial_second_eq]
  have hsum : (∑ n ∈ Ico 1 33, |(discriminant23CharacterCoefficient n : ℝ)| / (n : ℝ)) ≤ 6 := by
    exact_mod_cast coefficientWeights_checked
  have h := discriminant23_thetaScale_interval.1
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ Ico 1 33, 42 *
      (|(discriminant23CharacterCoefficient n : ℝ)| / (n : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (mem_Ico.mp hn).1
      have ha : (n : ℝ) ≤ discriminant23ThetaScale * n := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ discriminant23ThetaScale by linarith) hn₀.le
      have hMode := (modeSecond_abs_le (hn₀.trans_le ha) ht hu).trans
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 21) hn₀ ha)
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (mul_le_mul_of_nonneg_left hMode (by positivity)).trans_eq (by ring)
    _ ≤ 252 := by
      rw [← mul_sum]
      linarith

/-- The trapezoid approximation has a single error budget for both
endpoint heights and all real heights in between. -/
theorem discriminant23_characterFold_trapezoid_error {t : ℝ} (ht : |t| ≤ 11 / 2) :
    |(discriminant23CharacterFold ⟨1 / 2, t⟩).re -
      trapezoidal_integral (discriminant23CharacterLogPolynomial t) 1024 0 3| ≤
        7 / 12500 := by
  let f := discriminant23CharacterLogPolynomial t
  have hC : ContDiff ℝ 2 f := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ 2 * Real.exp (u / 2) * Real.cos (t * u) *
      discriminant23CharacterPolynomial (Real.exp (-discriminant23ThetaScale * Real.exp u)))
    unfold discriminant23CharacterPolynomial
    fun_prop
  have hDiff : UniqueDiffOn ℝ [[(0 : ℝ), 3]] := uniqueDiffOn_uIcc (by norm_num)
  have hb (u : ℝ) : |iteratedDerivWithin 2 f [[(0 : ℝ), 3]] u| ≤ 252 := by
    by_cases hu : u ∈ [[(0 : ℝ), 3]]
    · rw [iteratedDerivWithin_eq_iteratedDeriv hDiff hC.contDiffAt hu,
        iteratedDeriv_succ (n := 1), iteratedDeriv_one]
      have h₀ : 0 ≤ u := (mem_Icc.mp (by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] using hu)).1
      exact logPolynomial_second_abs_le ht h₀
    · rw [iteratedDerivWithin_succ (n := 1), derivWithin_zero_of_notMem_closure]
      · norm_num
      · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), closure_Icc] using hu
  have hT := trapezoidal_error_le_of_c2 (hC.contDiffOn) hb
    (show 0 < (1024 : ℕ) by decide)
  have hU : |(discriminant23CharacterFold ⟨1 / 2, t⟩).re -
      (∫ u in (0 : ℝ)..3, f u)| ≤ 1 / 100000 :=
    discriminant23_characterFold_logPolynomial_error t
  rw [trapezoidal_error] at hT
  calc
    _ = |((discriminant23CharacterFold ⟨1 / 2, t⟩).re - ∫ u in (0 : ℝ)..3, f u) +
      ((∫ u in (0 : ℝ)..3, f u) - trapezoidal_integral f 1024 0 3)| := by
        change |(discriminant23CharacterFold ⟨1 / 2, t⟩).re -
          trapezoidal_integral f 1024 0 3| = _
        congr 1
        ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_sub_comm (∫ u in (0 : ℝ)..3, f u)]
      norm_num at hT
      linarith only [hT, hU])

#check @discriminant23_characterFold_trapezoid_error
#print axioms discriminant23_characterFold_trapezoid_error

end

end FieldTarget
