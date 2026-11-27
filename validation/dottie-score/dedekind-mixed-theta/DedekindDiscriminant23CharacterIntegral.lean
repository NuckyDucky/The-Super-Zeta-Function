import DedekindDiscriminant23CharacterPolynomial
import DedekindDiscriminant23ZeroCounts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace FieldTarget

open NumberField MeasureTheory Set
open scoped NumberField Interval

noncomputable section

private def heat (x : ℝ) : ℝ := Real.exp (-discriminant23ThetaScale * x)

private def thetaDifference (q : ℝ) : ℝ :=
  classThetaStar discriminant23PrincipalForm q - classThetaStar discriminant23OtherForm q

private def radialWeight (t x : ℝ) : ℝ :=
  2 * Real.exp (-Real.log x / 2) * Real.cos (t * Real.log x)

private def radialReading (t x : ℝ) : ℝ := radialWeight t x * thetaDifference (heat x)

private def radialPolynomial (t x : ℝ) : ℝ :=
  radialWeight t x * discriminant23CharacterPolynomial (heat x)

/-- The finite integrand in the logarithmic radial coordinate. -/
def discriminant23CharacterLogPolynomial (t u : ℝ) : ℝ :=
  2 * Real.exp (u / 2) * Real.cos (t * u) *
    discriminant23CharacterPolynomial (heat (Real.exp u))

private theorem foldWeight_re_on_line (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (discriminant23FoldWeight ⟨1 / 2, t⟩ x).re = radialWeight t x := by
  have hPow (z : ℂ) : (x : ℂ) ^ z = Complex.exp (z * (Real.log x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, mul_comm]
  rw [discriminant23FoldWeight, hPow, hPow]
  simp only [Complex.add_re, Complex.exp_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, radialWeight]
  rw [show -t * Real.log x = -(t * Real.log x) by ring, Real.cos_neg]
  have h₁ : (1 / 2 - 1 : ℝ) * Real.log x = -Real.log x / 2 := by ring
  have h₂ : -(1 / 2 : ℝ) * Real.log x = -Real.log x / 2 := by ring
  rw [h₁, h₂]
  ring

private theorem radialReading_integrable_and_eq (t : ℝ) :
    IntegrableOn (radialReading t) (Ioi 1) ∧
      (discriminant23CharacterFold ⟨1 / 2, t⟩).re =
        ∫ x in Ioi 1, radialReading t x := by
  let F := (discriminant23QuadraticSubfield : Type)
  let w : ℂ := ⟨1 / 2, t⟩
  let c := discriminant23NormTwoClass
  let g (x : ℝ) :=
    discriminant23FoldWeight w x * discriminant23ClassKernel (1 : ClassGroup (𝓞 F)) x -
      discriminant23FoldWeight w x * discriminant23ClassKernel c x
  have hp := discriminant23_fold_integrable (1 : ClassGroup (𝓞 F)) w
  have hn := discriminant23_fold_integrable c w
  have hg : IntegrableOn g (Ioi 1) := hp.sub hn
  have he (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : (g x).re = radialReading t x := by
    dsimp only [g, c, F, w]
    rw [← mul_sub]
    rw [radialReading, ← foldWeight_re_on_line t (zero_lt_one.trans hx)]
    simp [discriminant23ClassKernel, discriminant23_normTwoClass_ne_one, ← Complex.ofReal_sub,
      Complex.mul_re, thetaDifference, heat]
  constructor
  · have hr : IntegrableOn (fun x ↦ (g x).re) (Ioi 1) :=
      Complex.reCLM.integrable_comp hg
    exact hr.congr_fun he measurableSet_Ioi
  · change (discriminant23CharacterFold w).re = _
    rw [discriminant23CharacterFold, discriminant23_classLambdaZero_eq_fold,
      discriminant23_classLambdaZero_eq_fold, ← integral_sub hp hn]
    change (∫ x in Ioi 1, g x).re = _
    calc
      _ = ∫ x in Ioi 1, (g x).re := (integral_re hg).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi he

theorem discriminant23_characterFold_re_eq_radialIntegral (t : ℝ) :
    (discriminant23CharacterFold ⟨1 / 2, t⟩).re =
      ∫ x in Ioi 1, radialReading t x :=
  (radialReading_integrable_and_eq t).2

private theorem heat_nonneg (x : ℝ) : 0 ≤ heat x := (Real.exp_pos _).le

private theorem heat_le_three_elevenths {x : ℝ} (hx : 1 ≤ x) : heat x ≤ 3 / 11 := by
  have ha := discriminant23_thetaScale_interval.1
  apply (Real.exp_le_exp.mpr ?_).trans discriminant23_thetaExp_interval.2
  nlinarith [mul_nonneg (show 0 ≤ discriminant23ThetaScale by linarith) (sub_nonneg.mpr hx)]

private theorem heat_le_decay {x : ℝ} (hx : 0 ≤ x) :
    heat x ≤ Real.exp (-(13 / 10 : ℝ) * x) := by
  have ha := discriminant23_thetaScale_interval.1
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ha) hx)

private theorem radialWeight_abs_le (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |radialWeight t x| ≤ 2 := by
  rw [radialWeight, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg (Real.exp_nonneg _)]
  have he : Real.exp (-Real.log x / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Real.log_nonneg hx])
  have h := mul_le_mul he (Real.abs_cos_le_one (t * Real.log x))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith only [h]

private theorem radialReading_abs_le (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |radialReading t x| ≤ (21 / 5) * Real.exp (-(13 / 10 : ℝ) * x) := by
  obtain ⟨hp₀, hp₁, hn₀, hn₁⟩ := discriminant23_classThetaStar_bounds
    (heat_nonneg x) (heat_le_three_elevenths hx)
  have hθ : 0 ≤ thetaDifference (heat x) := by
    dsimp [thetaDifference]
    linarith [heat_nonneg x]
  have hθ' : thetaDifference (heat x) ≤ (21 / 10) * heat x := by
    dsimp [thetaDifference]
    linarith
  rw [radialReading, abs_mul, abs_of_nonneg hθ]
  calc
    _ ≤ 2 * ((21 / 10) * heat x) :=
      mul_le_mul (radialWeight_abs_le t hx) hθ' hθ (by norm_num)
    _ = (21 / 5) * heat x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (heat_le_decay (by linarith)) (by norm_num)

private theorem radialPolynomial_error (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |radialReading t x - radialPolynomial t x| ≤
      (1 / 50000 : ℝ) * Real.exp (-(13 / 10 : ℝ) * x) := by
  rw [radialReading, radialPolynomial, ← mul_sub, abs_mul]
  have h := discriminant23_characterPolynomial_error (heat_nonneg x)
    (heat_le_three_elevenths hx)
  calc
    _ ≤ 2 * (heat x / 100000) :=
      mul_le_mul (radialWeight_abs_le t hx) h (abs_nonneg _) (by norm_num)
    _ = (1 / 50000 : ℝ) * heat x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (heat_le_decay (by linarith)) (by norm_num)

private theorem exp_three_ge_sixteen : (16 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem exp_neg_thirteen_tenths_le : Real.exp (-(13 / 10 : ℝ)) ≤ 3 / 11 := by
  have h := Real.sum_le_exp_of_nonneg (x := (13 / 10 : ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hlo : (11 / 3 : ℝ) ≤ Real.exp (13 / 10) := by linarith only [h]
  rw [Real.exp_neg, ← one_div, show (3 / 11 : ℝ) = 1 / (11 / 3) by norm_num]
  exact one_div_le_one_div_of_le (by norm_num) hlo

private theorem exp_far_decay_le :
    Real.exp (-(13 / 10 : ℝ) * Real.exp 3) ≤ 1 / 2 ^ 20 := by
  have h₁ : -(13 / 10 : ℝ) * Real.exp 3 ≤ -20 := by linarith [exp_three_ge_sixteen]
  have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-20) := Real.exp_le_exp.mpr h₁
    _ = 1 / Real.exp 1 ^ 20 := by
      rw [Real.exp_neg, show (20 : ℝ) = (20 : ℕ) * 1 by norm_num, Real.exp_nat_mul, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) h₂ _)

private theorem radialTail_le (t : ℝ) :
    |∫ x in Ioi (Real.exp 3), radialReading t x| ≤ 1 / 200000 := by
  have hMajor := (integrableOn_exp_mul_Ioi (a := -(13 / 10 : ℝ)) (by norm_num)
    (Real.exp 3)).const_mul (21 / 5 : ℝ)
  have hAbs := norm_integral_le_of_norm_le (f := radialReading t) hMajor
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      have hx' : Real.exp 3 < x := hx
      have hx₁ : 1 ≤ x := by linarith [exp_three_ge_sixteen]
      simpa only [Real.norm_eq_abs] using radialReading_abs_le t hx₁)
  rw [Real.norm_eq_abs, integral_const_mul,
    integral_exp_mul_Ioi (by norm_num : (-(13 / 10 : ℝ)) < 0)] at hAbs
  have hle := mul_le_mul_of_nonneg_left exp_far_decay_le (by norm_num : (0 : ℝ) ≤ 42 / 13)
  linarith [hAbs, hle]

private theorem radialPolynomial_continuousOn (t : ℝ) {s : Set ℝ}
    (hs : s ⊆ Ioi (0 : ℝ)) : ContinuousOn (radialPolynomial t) s := by
  have hl : ContinuousOn Real.log s := fun x hx ↦
    (Real.continuousAt_log (mem_Ioi.mp (hs hx)).ne').continuousWithinAt
  have hp : Continuous discriminant23CharacterPolynomial := by
    unfold discriminant23CharacterPolynomial
    fun_prop
  have hh : Continuous heat := by
    unfold heat
    fun_prop
  unfold radialPolynomial radialWeight
  exact ((continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
    (hl.neg.div_const 2))).mul (Real.continuous_cos.comp_continuousOn
      (continuousOn_const.mul hl))).mul (hp.comp_continuousOn hh.continuousOn)

private theorem logPolynomial_integral_eq (t : ℝ) :
    (∫ u in (0 : ℝ)..3, discriminant23CharacterLogPolynomial t u) =
      ∫ x in (1 : ℝ)..Real.exp 3, radialPolynomial t x := by
  have hc : ContinuousOn (radialPolynomial t) (Real.exp '' [[(0 : ℝ), 3]]) :=
    radialPolynomial_continuousOn t (by
      rintro _ ⟨u, _, rfl⟩
      exact Real.exp_pos u)
  have h := intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := 3)
    (fun u _ ↦ Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hc
  rw [Real.exp_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [Function.comp_apply, radialPolynomial, radialWeight,
    discriminant23CharacterLogPolynomial]
  rw [Real.log_exp]
  have e : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← e]
  ring

private theorem radialPolynomial_integral_error (t : ℝ) :
    |(∫ x in (1 : ℝ)..Real.exp 3, radialReading t x) -
      (∫ x in (1 : ℝ)..Real.exp 3, radialPolynomial t x)| ≤ 1 / 200000 := by
  let R := Real.exp 3
  have hR : 1 ≤ R := by dsimp [R]; linarith [exp_three_ge_sixteen]
  have hWhole := (radialReading_integrable_and_eq t).1
  have hSubset : Ioc (1 : ℝ) R ⊆ Ioi 1 := fun _ hx ↦ hx.1
  have hFull := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    (hWhole.mono_set hSubset)
  have hFin := (radialPolynomial_continuousOn t (s := Icc 1 R)
    (fun x hx ↦ zero_lt_one.trans_le hx.1)).intervalIntegrable_of_Icc (μ := volume) hR
  rw [← intervalIntegral.integral_sub hFull hFin, intervalIntegral.integral_of_le hR]
  let M (x : ℝ) := (1 / 50000 : ℝ) * Real.exp (-(13 / 10 : ℝ) * x)
  have hMajor : IntegrableOn M (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (a := -(13 / 10 : ℝ)) (by norm_num) 1).const_mul _
  have hAbs := norm_integral_le_of_norm_le (f := fun x ↦ radialReading t x - radialPolynomial t x)
    (hMajor.mono_set hSubset)
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using radialPolynomial_error t hx.1.le)
  have hSub : (∫ x in Ioc (1 : ℝ) R, M x) ≤ ∫ x in Ioi (1 : ℝ), M x :=
    setIntegral_mono_set hMajor (ae_of_all _ (fun x ↦ by dsimp [M]; positivity))
      (Filter.Eventually.of_forall fun x hx ↦ hSubset hx)
  rw [Real.norm_eq_abs] at hAbs
  refine (hAbs.trans hSub).trans ?_
  rw [show (∫ x in Ioi (1 : ℝ), M x) = (1 / 50000 : ℝ) *
      (∫ x in Ioi (1 : ℝ), Real.exp (-(13 / 10 : ℝ) * x)) by exact integral_const_mul _ _,
    integral_exp_mul_Ioi (by norm_num : (-(13 / 10 : ℝ)) < 0), mul_one]
  linarith [exp_neg_thirteen_tenths_le]

/-- The finite logarithmic integral approximates the actual character fold
at every real height with a uniform absolute error. -/
theorem discriminant23_characterFold_logPolynomial_error (t : ℝ) :
    |(discriminant23CharacterFold ⟨1 / 2, t⟩).re -
      (∫ u in (0 : ℝ)..3, discriminant23CharacterLogPolynomial t u)| ≤ 1 / 100000 := by
  rw [discriminant23_characterFold_re_eq_radialIntegral, logPolynomial_integral_eq]
  have hFull := (radialReading_integrable_and_eq t).1
  have hR : (1 : ℝ) ≤ Real.exp 3 := by linarith [exp_three_ge_sixteen]
  rw [← intervalIntegral.integral_interval_add_Ioi hFull (hFull.mono_set (Ioi_subset_Ioi hR)),
    add_sub_right_comm]
  exact (abs_add_le _ _).trans (by
    linarith [radialTail_le t, radialPolynomial_integral_error t])

#check @discriminant23_characterFold_logPolynomial_error
#print axioms discriminant23_characterFold_re_eq_radialIntegral
#print axioms discriminant23_characterFold_logPolynomial_error

end

end FieldTarget
